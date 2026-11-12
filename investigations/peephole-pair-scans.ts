import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { isDeepStrictEqual } from 'node:util';
import ts from 'typescript';
import { Project, ScriptTarget } from 'ts-morph';
import { extractModule } from '../tools/src/extract.ts';
import { resolveModule } from '../tools/src/resolve.ts';
import { narrowModule } from '../tools/src/narrow.ts';
import {
  transformModuleDafny,
  transformModuleLean,
} from '../tools/src/transform.ts';
import type { Module, Stmt } from '../tools/src/ir.ts';

// Pin the old optimizer so the independent constructor/map fix cannot explain a difference.
const baseline = execFileSync(
  'git',
  ['show', '36eb31d:tools/src/peephole.ts'],
  { encoding: 'utf8' },
);
const scan = 'return rewriteStmtListPairs(stmts.map(peepholeStmt));';
assert(baseline.includes(scan));
const repeated = baseline.replace(
  scan,
  `
  let current = stmts.map(peepholeStmt);
  for (;;) {
    const next = rewriteStmtListPairs(current);
    if (next.length === current.length) return next;
    current = next;
  }
`,
);

async function optimizer(source: string) {
  const withImport = source.replaceAll(
    '"./ir.js"',
    JSON.stringify(pathToFileURL(resolve('tools/src/ir.ts')).href),
  );
  const output = ts.transpileModule(withImport, {
    compilerOptions: {
      target: ts.ScriptTarget.ESNext,
      module: ts.ModuleKind.ESNext,
    },
  }).outputText;
  const loaded = await import(
    `data:text/javascript;base64,${Buffer.from(output).toString('base64')}`
  );
  return loaded.peepholeModule as (
    mod: Module,
    backend: 'lean' | 'dafny',
  ) => Module;
}
const noPairs = await optimizer(
  baseline.replace(scan, 'return stmts.map(peepholeStmt);'),
);
const once = await optimizer(baseline);
const fixpoint = await optimizer(repeated);

const sources: { name: string; text: string }[] = [];
for (const count of [1, 2, 3, 4])
  for (const binding of ['const', 'let'])
    for (const live of [false, true])
      for (const nested of [false, true]) {
        const name = `case_${count}_${binding}_${live}_${nested}`;
        const pairs = Array.from(
          { length: count },
          (_, i) => `
          ${binding} x${i} = m.get("${i}");
          if (x${i} !== undefined) { total += x${i}; } else { total += 0; }
        `,
        ).join('\n');
        const tail = live ? 'if (x0 !== undefined) { total += x0; }' : '';
        sources.push({
          name,
          text: `export function ${name}(m: Map<string, number>, enabled: boolean): number {
          let total = 0;
          ${nested ? `if (enabled) { ${pairs} ${tail} }` : pairs + tail}
          return total;
        }`,
        });
      }
sources.push({
  name: 'shadow',
  text: `export function shadow(m: Map<string, number>, enabled: boolean): number {
    let total = 0;
    const x = m.get("outer");
    if (x !== undefined) { total += x; }
    if (enabled) {
      const x = m.get("inner");
      if (x !== undefined) { total += x; }
    }
    return total;
  }`,
});
sources.push({
  name: 'mutated',
  text: `export function mutated(m: Map<string, number>): number {
    let x = m.get("a");
    x = m.get("b");
    if (x !== undefined) { return x; }
    return 0;
  }`,
});
const positiveSources: { name: string; text: string }[] = [];
positiveSources.push({
  name: 'blocks',
  text: `export function blocks(m: Map<string, number>): number {
    let total = 0;
    { const x = m.get("a"); if (x !== undefined) { total += x; } else { total += 0; } }
    { const x = m.get("b"); if (x !== undefined) { total += x; } else { total += 0; } }
    return total;
  }`,
});
positiveSources.push({
  name: 'fallthrough',
  text: `export function fallthrough(m: Map<string, number>, k: string): number {
    let total = 0;
    switch (k) {
      case "a": {
        const x = m.get("a");
        if (x !== undefined) { total += x; } else { total += 0; }
      }
      case "b": {
        const x = m.get("b");
        if (x !== undefined) { total += x; } else { total += 0; }
        break;
      }
      default: { total += 0; break; }
    }
    return total;
  }`,
});

const project = new Project({
  compilerOptions: {
    strict: true,
    target: ScriptTarget.ESNext,
    lib: ['lib.esnext.d.ts'],
    types: [],
    skipLibCheck: true,
  },
});
const file = project.createSourceFile(
  'pair-scan-experiment.ts',
  sources.map(s => s.text).join('\n'),
);
const positiveFile = project.createSourceFile(
  'pair-scan-positive.ts',
  positiveSources.map(s => s.text).join('\n'),
);
assert.deepEqual(
  project.getPreEmitDiagnostics().map(d => d.getMessageText()),
  [],
);
const typed = narrowModule(resolveModule(extractModule(file)));
const positiveTyped = narrowModule(resolveModule(extractModule(positiveFile)));
function affectedBody(mod: Module, name: string): Stmt[] {
  const method = mod.decls.find(d => d.kind === 'method' && d.name === name);
  assert(method?.kind === 'method');
  if (name === 'blocks') return method.body.slice(1, -1);
  const match = method.body[1];
  assert(match?.kind === 'match');
  const arm = match.arms[0];
  assert.deepEqual(arm?.pattern, { kind: 'literal', value: 'a' });
  return arm.body;
}

let backendComparisons = 0;
let backendsExercisingPairMerges = 0;
let negativeSourceDifferences = 0;
let supportedPositiveDifferences = 0;
for (const [backend, transform] of [
  ['dafny', transformModuleDafny],
  ['lean', transformModuleLean],
] as const) {
  const input = transform(typed).defFile;
  const first = once(input, backend);
  assert.notDeepEqual(
    first,
    noPairs(input, backend),
    `${backend}: source exercises pair merging`,
  );
  backendsExercisingPairMerges++;
  const second = once(first, backend);
  negativeSourceDifferences += first.decls.filter(
    (decl, i) => !isDeepStrictEqual(decl, second.decls[i]),
  ).length;
  assert.deepEqual(second, first, `${backend}: second complete invocation`);
  assert.deepEqual(
    fixpoint(input, backend),
    first,
    `${backend}: repeated scan`,
  );
  const mutableControl = input.decls.find(
    d => d.kind === 'method' && d.name === 'case_2_let_false_false',
  );
  assert(mutableControl?.kind === 'method');
  assert.deepEqual(
    mutableControl.body.flatMap(
      s => s.kind === 'let' && s.name.startsWith('x') ? [s.mutable] : [],
    ),
    [true, true],
    `${backend}: unassigned let remains a mutable negative control`,
  );

  const positiveInput = transform(positiveTyped).defFile;
  const positiveFirst = once(positiveInput, backend);
  const positiveSecond = once(positiveFirst, backend);
  assert.deepEqual(fixpoint(positiveInput, backend), positiveSecond);
  assert.deepEqual(once(positiveSecond, backend), positiveSecond);
  for (const { name } of positiveSources) {
    const before = affectedBody(positiveInput, name);
    const afterOne = affectedBody(positiveFirst, name);
    const afterTwo = affectedBody(positiveSecond, name);
    const differs = !isDeepStrictEqual(afterOne, afterTwo);
    supportedPositiveDifferences += Number(differs);
    assert(differs, `${backend}: ${name} needs a second scan`);
    assert.deepEqual(before.map(s => s.kind), ['let', 'match', 'let', 'match']);
    assert.deepEqual(afterOne.map(s => s.kind), ['let', 'match', 'if']);
    assert.deepEqual(afterTwo.map(s => s.kind), ['if', 'if']);
    for (const [i, key] of ['a', 'b'].entries()) {
      const stmt = afterTwo[i];
      assert(stmt?.kind === 'if' && stmt.cond.kind === 'methodCall');
      assert.equal(stmt.cond.method, 'has');
      assert.deepEqual(stmt.cond.obj, { kind: 'var', name: 'm' });
      assert.deepEqual(stmt.cond.args, [{ kind: 'str', value: key }]);
    }
    assert.deepEqual(afterTwo[1], afterOne[2]);
  }
  backendComparisons++;
  if (process.env.PAIR_SCAN_EVIDENCE_DIR) {
    for (const [stage, value] of [
      ['input', input],
      ['first', first],
      ['second', second],
      ['positive-input', positiveInput],
      ['positive-first', positiveFirst],
      ['positive-second', positiveSecond],
    ] as const)
      writeFileSync(
        resolve(process.env.PAIR_SCAN_EVIDENCE_DIR, `${backend}-${stage}.json`),
        JSON.stringify(value, null, 2),
      );
  }
}

const variable = (name: string) => ({ kind: 'var' as const, name });
const pair = (name: string, value: string): Stmt[] => [
  {
    kind: 'let',
    name,
    mutable: false,
    type: { kind: 'optional', inner: { kind: 'int' } },
    value: {
      kind: 'methodCall',
      obj: variable('m'),
      objTy: { kind: 'map', key: { kind: 'string' }, value: { kind: 'int' } },
      method: 'get',
      args: [{ kind: 'str', value }],
      monadic: false,
    },
  },
  {
    kind: 'match',
    scrutinee: variable(name),
    arms: [
      { pattern: { kind: 'ctor', ctor: 'some', binders: ['_'] }, body: [] },
      { pattern: { kind: 'ctor', ctor: 'none', binders: [] }, body: [] },
    ],
  },
];
let syntheticDifferences = 0;
for (const backend of ['dafny', 'lean'] as const) {
  for (const duplicate of [false, true]) {
    const input: Module = {
      comment: '',
      imports: [],
      options: [],
      decls: [
        {
          kind: 'method',
          name: 'synthetic',
          typeParams: [],
          params: [
            {
              name: 'm',
              type: {
                kind: 'map',
                key: { kind: 'string' },
                value: { kind: 'int' },
              },
            },
          ],
          returnType: { kind: 'void' },
          requires: [],
          ensures: [],
          decreases: null,
          body: [...pair('x', 'a'), ...pair(duplicate ? 'x' : 'y', 'b')],
        },
      ],
    };
    const first = once(input, backend);
    const second = once(first, backend);
    assert.equal(JSON.stringify(first) !== JSON.stringify(second), duplicate);
    assert.deepEqual(fixpoint(input, backend), second);
    if (duplicate) syntheticDifferences++;
  }
}
console.log(
  JSON.stringify({
    baseline: '36eb31d',
    negativeSourceFunctions: sources.length,
    positiveSourceFunctions: positiveSources.length,
    backendComparisons,
    backendsExercisingPairMerges,
    negativeSourceDifferences,
    supportedPositiveDifferences,
    syntheticDuplicateNameDifferences: syntheticDifferences,
  }),
);
