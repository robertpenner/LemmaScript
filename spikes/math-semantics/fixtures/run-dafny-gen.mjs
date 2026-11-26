#!/usr/bin/env node
// Copies each fixture into an output directory outside the repository and runs
// `lsc gen --backend=dafny` on the copy, so no generated .dfy files land in the
// tracked tree. Prints one JSON line per fixture with the exit code and either
// the emitted Dafny for `f` or the error text.
//
// Usage (from the repository root):
//   node spikes/math-semantics/fixtures/run-dafny-gen.mjs <out-dir>

import { spawnSync } from 'node:child_process';
import { copyFileSync, existsSync, mkdirSync, readdirSync, readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(here, '..', '..', '..');
const outDir = process.argv[2];
if (!outDir) {
  console.error('usage: run-dafny-gen.mjs <out-dir>');
  process.exit(2);
}
const absOut = resolve(outDir);
if (absOut.startsWith(repoRoot + '/') || absOut === repoRoot) {
  console.error('refusing to write generated files inside the repository');
  process.exit(2);
}
mkdirSync(absOut, { recursive: true });

const lsc = join(repoRoot, 'tools', 'src', 'lsc.ts');
const fixtures = readdirSync(here)
  .filter((f) => f.endsWith('.ts'))
  .sort();

for (const file of fixtures) {
  const target = join(absOut, file);
  copyFileSync(join(here, file), target);
  const r = spawnSync('npx', ['tsx', lsc, 'gen', '--backend=dafny', target], {
    cwd: repoRoot,
    encoding: 'utf8',
  });
  const gen = target.replace(/\.ts$/, '.dfy.gen');
  let emitted = null;
  if (r.status === 0 && existsSync(gen)) {
    emitted = readFileSync(gen, 'utf8')
      .split('\n')
      .filter((l) => /^(function|method|predicate)\b/.test(l) || /^\s{2}\S/.test(l))
      .join('\n');
  }
  const error = (r.stderr + r.stdout)
    .split('\n')
    .filter((l) => /error/i.test(l))
    .join('\n');
  console.log(JSON.stringify({ fixture: file, exit: r.status, emitted, error: error || null }));
}
