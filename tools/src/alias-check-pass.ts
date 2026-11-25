/**
 * Intra-procedural live-alias mutation checker (`midspiral/LemmaScript#387`,
 * Milestone 3b / `robertpenner/LemmaScript#50`).
 *
 * Mirrors `NoLiveAliasAtTarget` in `formal/narrowing-model.dfy`:
 *   - Read-only aliases (`const b = a; return a.length + b.length`) are ALLOWED.
 *   - Dead-source moves (`const b = a; b.push(1); return b.length`) are ALLOWED.
 *   - Live-alias mutations (`const b = a; b.push(1); return a.length`) are
 *     REJECTED with a diagnostic naming both bindings.
 *
 * Uses the self-verified alias conflict kernel from `alias-check.ts`.
 */

import type { TExpr, TFunction, TModule, TStmt, Ty } from "./typedir.js";
import type { TypeDeclInfo } from "./types.js";
import { declOfTy } from "./typedecls.js";
import { isMutatingCollectionMethod } from "./place-lowering.js";
import { bindCopyGroup, bindFreshGroup, findLiveAliasConflict } from "./alias-check.js";

export interface LiveAliasConflict {
  fn: string;
  mutatedVar: string;
  liveAlias: string;
  detail: string;
}

type AliasMap = Map<string, number>;

interface AliasState {
  map: AliasMap;
  nextId: number;
}

/** True for JS types whose values have mutable reference identity in JS
 *  (arrays, maps, sets, tuples, records, discriminated unions, and optionals
 *  wrapping them). Primitives and string-unions are immutable values. */
export function isMutableRefTy(ty: Ty, typeDecls: TypeDeclInfo[]): boolean {
  switch (ty.kind) {
    case "array":
    case "map":
    case "set":
    case "tuple":
      return true;
    case "optional":
      return isMutableRefTy(ty.inner, typeDecls);
    case "user": {
      const decl = declOfTy(typeDecls, ty);
      if (!decl) return false;
      if (decl.kind === "string-union" || decl.kind === "opaque") return false;
      if (decl.kind === "alias") return decl.aliasOfTy ? isMutableRefTy(decl.aliasOfTy, typeDecls) : false;
      return true; // record or discriminated-union
    }
    default:
      return false;
  }
}

/** Root variable of a pure access path `x`, `x.a`, `x.a.b` (or null). */
function accessPathRoot(e: TExpr): string | null {
  if (e.kind === "var") return e.name;
  if (e.kind === "field") return accessPathRoot(e.obj);
  return null;
}

/** If `expr` aliases an existing mutable-ref variable (direct `var` copy,
 *  e.g. `const b = a`, or field/index/map projection from a mutable-ref root),
 *  return that source root variable name; otherwise null.
 *
 *  Note: we intentionally track direct variable copies (`const b = a`) and
 *  field/element aliases (`const sub = box.items`, `const row = m.get(k)`)
 *  when the extracted value is itself a mutable reference type. */
function aliasSourceRoot(e: TExpr, typeDecls: TypeDeclInfo[]): string | null {
  if ("freshClone" in e && e.freshClone) return null;
  if (!isMutableRefTy(e.ty, typeDecls)) return null;
  switch (e.kind) {
    case "var":
      return e.name === "undefined" || e.name === "null" ? null : e.name;
    case "field":
      return aliasSourceRoot(e.obj, typeDecls);
    case "index":
      return aliasSourceRoot(e.obj, typeDecls);
    case "call":
      if (e.fn.kind === "field" && e.fn.field === "get" && e.fn.obj.ty.kind === "map") {
        return accessPathRoot(e.fn.obj);
      }
      return null;
    default:
      return null;
  }
}

// ── Free variable collection ────────────────────────────────

function collectFreeVarsExpr(e: TExpr, out: Set<string>): void {
  switch (e.kind) {
    case "var":
      if (e.name !== "undefined" && e.name !== "null" && e.name !== "\\result") out.add(e.name);
      return;
    case "num": case "bigint": case "str": case "bool": case "havoc":
      return;
    case "binop":
      collectFreeVarsExpr(e.left, out);
      collectFreeVarsExpr(e.right, out);
      return;
    case "unop":
      collectFreeVarsExpr(e.expr, out);
      return;
    case "call":
      collectFreeVarsExpr(e.fn, out);
      for (const a of e.args) collectFreeVarsExpr(a, out);
      return;
    case "index":
      collectFreeVarsExpr(e.obj, out);
      collectFreeVarsExpr(e.idx, out);
      return;
    case "field":
      collectFreeVarsExpr(e.obj, out);
      return;
    case "record":
      if (e.spread) collectFreeVarsExpr(e.spread, out);
      for (const f of e.fields) collectFreeVarsExpr(f.value, out);
      return;
    case "arrayLiteral":
      for (const el of e.elems) collectFreeVarsExpr(el, out);
      return;
    case "lambda": {
      const inner = liveBeforeStmts(e.body, new Set(), new Set());
      for (const p of e.params) inner.delete(p.name);
      for (const v of inner) out.add(v);
      return;
    }
    case "conditional":
      collectFreeVarsExpr(e.cond, out);
      collectFreeVarsExpr(e.then, out);
      collectFreeVarsExpr(e.else, out);
      return;
    case "optChain":
      collectFreeVarsExpr(e.obj, out);
      for (const step of e.chain) {
        if (step.kind === "call") for (const a of step.args) collectFreeVarsExpr(a, out);
        else if (step.kind === "index") collectFreeVarsExpr(step.idx, out);
      }
      return;
    case "nullish":
      collectFreeVarsExpr(e.left, out);
      collectFreeVarsExpr(e.right, out);
      return;
    case "someMatch":
      collectFreeVarsExpr(e.scrutinee, out);
      {
        const sb = new Set<string>();
        collectFreeVarsExpr(e.someBody, sb);
        sb.delete(e.binder);
        for (const v of sb) out.add(v);
      }
      collectFreeVarsExpr(e.noneBody, out);
      return;
    case "tagMatch":
      collectFreeVarsExpr(e.scrutinee, out);
      for (const c of e.cases) collectFreeVarsExpr(c.body, out);
      if (e.fallthrough) collectFreeVarsExpr(e.fallthrough, out);
      return;
    case "forall":
    case "exists": {
      const inner = new Set<string>();
      collectFreeVarsExpr(e.body, inner);
      inner.delete(e.var);
      for (const v of inner) out.add(v);
      return;
    }
  }
}

function freeVarsExpr(e: TExpr): Set<string> {
  const s = new Set<string>();
  collectFreeVarsExpr(e, s);
  return s;
}

function unionSets(...sets: ReadonlySet<string>[]): Set<string> {
  const out = new Set<string>();
  for (const s of sets) for (const v of s) out.add(v);
  return out;
}

function setsEqual(a: ReadonlySet<string>, b: ReadonlySet<string>): boolean {
  if (a.size !== b.size) return false;
  for (const v of a) if (!b.has(v)) return false;
  return true;
}

// ── In-place mutation target detection ──────────────────────

/** If statement `s` mutates a storage variable in place (rather than merely
 *  rebinding a local variable to a fresh object), return the mutated root
 *  variable name; otherwise null. */
function mutatedRootOfStmt(s: TStmt): string | null {
  if (s.kind === "expr") {
    const e = s.expr;
    if (e.kind === "call" && e.fn.kind === "field" && isMutatingCollectionMethod(e.fn.obj.ty, e.fn.field)) {
      return accessPathRoot(e.fn.obj);
    }
    // Optional chaining mutation before narrow: `m.get(k)?.push(v)` or `arr?.push(v)`
    if (e.kind === "optChain" && e.chain.length >= 2) {
      const last = e.chain[e.chain.length - 1]!;
      const prev = e.chain[e.chain.length - 2]!;
      if (last.kind === "call" && prev.kind === "field") {
        const method = prev.name;
        if (["push", "unshift", "sort", "set", "add", "delete"].includes(method)) {
          if (e.obj.kind === "call" && e.obj.fn.kind === "field" && e.obj.fn.field === "get") {
            return accessPathRoot(e.obj.fn.obj);
          }
          return accessPathRoot(e.obj);
        }
      }
    }
    // Post-narrow `m.get(k)?.push(v)` lowered to expression `someMatch`
    if (e.kind === "someMatch" &&
        e.scrutinee.kind === "call" && e.scrutinee.fn.kind === "field" &&
        e.scrutinee.fn.field === "get" && e.scrutinee.fn.obj.ty.kind === "map" &&
        e.someBody.kind === "call" && e.someBody.fn.kind === "field" &&
        ["push", "unshift", "sort", "set", "add", "delete"].includes(e.someBody.fn.field)) {
      return accessPathRoot(e.scrutinee.fn.obj);
    }
    return null;
  }
  if (s.kind === "let" && s.init.kind === "call" && s.init.fn.kind === "field" &&
      (s.init.fn.field === "pop" || s.init.fn.field === "shift") && s.init.fn.obj.ty.kind === "array") {
    return accessPathRoot(s.init.fn.obj);
  }
  if (s.kind === "assign") {
    if (s.value.kind === "call" && s.value.fn.kind === "field" &&
        (s.value.fn.field === "pop" || s.value.fn.field === "shift") && s.value.fn.obj.ty.kind === "array") {
      return accessPathRoot(s.value.fn.obj);
    }
    // Non-`this.` dotted field assignment (`b.count = ...`): mutates root `b` in place.
    if (s.target.includes(".") && !s.target.startsWith("this.")) {
      return s.target.split(".")[0]!;
    }
    // Array index assignment (`arr[i] = v` desugared to `arr = arr.with(i, v)`): mutates `arr` in place.
    if (s.value.kind === "call" && s.value.fn.kind === "field" && s.value.fn.field === "with" &&
        s.value.fn.obj.kind === "var" && s.value.fn.obj.name === s.target) {
      return s.target;
    }
    return null;
  }
  return null;
}

// ── Backward liveness analysis ──────────────────────────────

function liveBeforeStmt(s: TStmt, liveAfter: ReadonlySet<string>, ensuresVars: ReadonlySet<string>): Set<string> {
  switch (s.kind) {
    case "return":
      return unionSets(freeVarsExpr(s.value), ensuresVars);
    case "throw":
      return new Set();
    case "break":
    case "continue":
      return new Set(liveAfter);
    case "let": {
      const next = new Set(liveAfter);
      next.delete(s.name);
      return unionSets(next, freeVarsExpr(s.init));
    }
    case "ghostLet": {
      const next = new Set(liveAfter);
      next.delete(s.name);
      return unionSets(next, freeVarsExpr(s.init));
    }
    case "assign": {
      const mutated = mutatedRootOfStmt(s);
      const next = new Set(liveAfter);
      if (mutated) {
        next.add(mutated);
      } else if (!s.target.includes(".")) {
        next.delete(s.target);
      }
      return unionSets(next, freeVarsExpr(s.value));
    }
    case "ghostAssign": {
      const next = new Set(liveAfter);
      next.delete(s.target);
      return unionSets(next, freeVarsExpr(s.value));
    }
    case "expr":
      return unionSets(liveAfter, freeVarsExpr(s.expr));
    case "assert":
      return unionSets(liveAfter, freeVarsExpr(s.expr));
    case "if":
      return unionSets(
        freeVarsExpr(s.cond),
        liveBeforeStmts(s.then, liveAfter, ensuresVars),
        liveBeforeStmts(s.else, liveAfter, ensuresVars),
      );
    case "someMatch": {
      const someLive = liveBeforeStmts(s.someBody, liveAfter, ensuresVars);
      someLive.delete(s.binder);
      return unionSets(
        freeVarsExpr(s.scrutinee),
        someLive,
        liveBeforeStmts(s.noneBody, liveAfter, ensuresVars),
      );
    }
    case "tagMatch": {
      const parts: Set<string>[] = [freeVarsExpr(s.scrutinee), liveBeforeStmts(s.fallthrough, liveAfter, ensuresVars)];
      for (const c of s.cases) parts.push(liveBeforeStmts(c.body, liveAfter, ensuresVars));
      return unionSets(...parts);
    }
    case "switch": {
      const parts: Set<string>[] = [freeVarsExpr(s.expr), liveBeforeStmts(s.defaultBody, liveAfter, ensuresVars)];
      for (const c of s.cases) parts.push(liveBeforeStmts(c.body, liveAfter, ensuresVars));
      return unionSets(...parts);
    }
    case "while": {
      const headVars = unionSets(
        freeVarsExpr(s.cond),
        ...s.invariants.map(freeVarsExpr),
        ...(s.decreases ? [freeVarsExpr(s.decreases)] : []),
        ...(s.doneWith ? [freeVarsExpr(s.doneWith)] : []),
      );
      let loopLive = unionSets(liveAfter, headVars);
      for (let iter = 0; iter < 32; iter++) {
        const next = unionSets(loopLive, liveBeforeStmts(s.body, loopLive, ensuresVars));
        if (setsEqual(next, loopLive)) break;
        loopLive = next;
      }
      return loopLive;
    }
    case "forof": {
      const headVars = unionSets(
        freeVarsExpr(s.iterable),
        ...s.invariants.map(freeVarsExpr),
        ...(s.doneWith ? [freeVarsExpr(s.doneWith)] : []),
      );
      let loopLive = unionSets(liveAfter, headVars);
      for (let iter = 0; iter < 32; iter++) {
        const bodyLive = liveBeforeStmts(s.body, loopLive, ensuresVars);
        for (const n of s.names) bodyLive.delete(n);
        bodyLive.delete(s.idx);
        const next = unionSets(loopLive, bodyLive);
        if (setsEqual(next, loopLive)) break;
        loopLive = next;
      }
      return loopLive;
    }
  }
}

function liveBeforeStmts(stmts: readonly TStmt[], liveAfter: ReadonlySet<string>, ensuresVars: ReadonlySet<string>): Set<string> {
  let cur = new Set(liveAfter);
  for (let i = stmts.length - 1; i >= 0; i--) {
    cur = liveBeforeStmt(stmts[i]!, cur, ensuresVars);
  }
  return cur;
}

/** Precompute `liveAfter[i]` for every statement `stmts[i]`. */
function computeStmtLiveAfter(stmts: readonly TStmt[], liveAfterBlock: ReadonlySet<string>, ensuresVars: ReadonlySet<string>): Set<string>[] {
  const result: Set<string>[] = new Array(stmts.length);
  let cur = new Set(liveAfterBlock);
  for (let i = stmts.length - 1; i >= 0; i--) {
    result[i] = cur;
    cur = liveBeforeStmt(stmts[i]!, cur, ensuresVars);
  }
  return result;
}

// ── Conservative alias-map join (union-find over equivalence classes) ──

function joinAliasStates(states: AliasState[]): AliasState {
  if (states.length === 0) return { map: new Map(), nextId: 0 };
  if (states.length === 1) return { map: new Map(states[0]!.map), nextId: states[0]!.nextId };

  const allVars = new Set<string>();
  let nextId = 0;
  for (const st of states) {
    if (st.nextId > nextId) nextId = st.nextId;
    for (const k of st.map.keys()) allVars.add(k);
  }

  const parent = new Map<string, string>();
  for (const v of allVars) parent.set(v, v);
  const find = (x: string): string => {
    let r = x;
    while (parent.get(r)! !== r) r = parent.get(r)!;
    let cur = x;
    while (cur !== r) {
      const p = parent.get(cur)!;
      parent.set(cur, r);
      cur = p;
    }
    return r;
  };
  const unite = (a: string, b: string): void => {
    const ra = find(a);
    const rb = find(b);
    if (ra !== rb) parent.set(ra, rb);
  };

  // If two variables share an alias group in ANY incoming branch, they may alias after the join.
  for (const st of states) {
    const byGroup = new Map<number, string>();
    for (const [v, g] of st.map.entries()) {
      const rep = byGroup.get(g);
      if (rep !== undefined) unite(rep, v);
      else byGroup.set(g, v);
    }
  }

  const rootToId = new Map<string, number>();
  const joined: AliasMap = new Map();
  for (const v of allVars) {
    const r = find(v);
    let id = rootToId.get(r);
    if (id === undefined) {
      id = nextId++;
      rootToId.set(r, id);
    }
    joined.set(v, id);
  }
  return { map: joined, nextId };
}

function aliasMapsEqual(a: AliasMap, b: AliasMap): boolean {
  if (a.size !== b.size) return false;
  // Compare equivalence partitions (group IDs may be renumbered by join).
  for (const [k1, g1] of a.entries()) {
    if (!b.has(k1)) return false;
    const b1 = b.get(k1)!;
    for (const [k2, g2] of a.entries()) {
      if ((g1 === g2) !== (b1 === b.get(k2)!)) return false;
    }
  }
  return true;
}

// ── Forward alias analysis + live-conflict checking ─────────

function checkStmts(
  stmts: readonly TStmt[],
  state: AliasState,
  liveAfterBlock: ReadonlySet<string>,
  ensuresVars: ReadonlySet<string>,
  typeDecls: TypeDeclInfo[],
  fnName: string,
  out: LiveAliasConflict[],
): AliasState {
  const liveAfterList = computeStmtLiveAfter(stmts, liveAfterBlock, ensuresVars);
  let cur: AliasState = { map: new Map(state.map), nextId: state.nextId };

  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i]!;
    const liveAfter = liveAfterList[i]!;

    // 1. Check for live-alias conflict if this statement mutates a root in place.
    const mutated = mutatedRootOfStmt(s);
    if (mutated && cur.map.has(mutated)) {
      const candidates = [...cur.map.keys()];
      const conflict = findLiveAliasConflict(mutated, cur.map, liveAfter, candidates);
      if (conflict !== "") {
        out.push({
          fn: fnName,
          mutatedVar: mutated,
          liveAlias: conflict,
          detail:
            `Live-alias mutation in \`${fnName}\`: mutating \`${mutated}\` in place while alias ` +
            `\`${conflict}\` is still observed afterward. LemmaScript models arrays, maps, sets, ` +
            `and records as immutable values, so mutating \`${mutated}\` would not update \`${conflict}\` ` +
            `(clone explicitly or mutate through a single live binding).`,
        });
      }
    }

    // 2. Advance alias state according to statement kind.
    switch (s.kind) {
      case "let": {
        if (isMutableRefTy(s.ty, typeDecls)) {
          const src = aliasSourceRoot(s.init, typeDecls);
          if (src && cur.map.has(src)) {
            cur = { map: bindCopyGroup(cur.map, s.name, src, cur.nextId), nextId: cur.nextId + 1 };
          } else {
            cur = { map: bindFreshGroup(cur.map, s.name, cur.nextId), nextId: cur.nextId + 1 };
          }
        }
        break;
      }
      case "assign": {
        // Whole-variable reassignment (not in-place mutation) updates alias membership.
        if (!mutated && !s.target.includes(".")) {
          if (isMutableRefTy(s.value.ty, typeDecls)) {
            const src = aliasSourceRoot(s.value, typeDecls);
            if (src && cur.map.has(src)) {
              cur = { map: bindCopyGroup(cur.map, s.target, src, cur.nextId), nextId: cur.nextId + 1 };
            } else {
              cur = { map: bindFreshGroup(cur.map, s.target, cur.nextId), nextId: cur.nextId + 1 };
            }
          } else if (cur.map.has(s.target)) {
            // Reassigned to undefined/primitive -> unaliases from prior group.
            cur = { map: bindFreshGroup(cur.map, s.target, cur.nextId), nextId: cur.nextId + 1 };
          }
        }
        break;
      }
      case "if": {
        const thenOut = checkStmts(s.then, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
        const elseOut = checkStmts(s.else, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
        cur = joinAliasStates([thenOut, elseOut]);
        break;
      }
      case "someMatch": {
        const someOut = checkStmts(s.someBody, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
        const noneOut = checkStmts(s.noneBody, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
        cur = joinAliasStates([someOut, noneOut]);
        break;
      }
      case "tagMatch": {
        const outs: AliasState[] = s.cases.map(c => checkStmts(c.body, cur, liveAfter, ensuresVars, typeDecls, fnName, out));
        outs.push(checkStmts(s.fallthrough, cur, liveAfter, ensuresVars, typeDecls, fnName, out));
        cur = joinAliasStates(outs);
        break;
      }
      case "switch": {
        const outs: AliasState[] = s.cases.map(c => checkStmts(c.body, cur, liveAfter, ensuresVars, typeDecls, fnName, out));
        outs.push(checkStmts(s.defaultBody, cur, liveAfter, ensuresVars, typeDecls, fnName, out));
        cur = joinAliasStates(outs);
        break;
      }
      case "while": {
        const loopLiveAfter = liveBeforeStmt(s, liveAfter, ensuresVars);
        let loopIn = cur;
        for (let iter = 0; iter < 16; iter++) {
          const dummyOut: LiveAliasConflict[] = [];
          const bodyOut = checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, typeDecls, fnName, dummyOut);
          const merged = joinAliasStates([loopIn, bodyOut]);
          if (aliasMapsEqual(merged.map, loopIn.map)) break;
          loopIn = merged;
        }
        checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, typeDecls, fnName, out);
        cur = loopIn;
        break;
      }
      case "forof": {
        const loopLiveAfter = liveBeforeStmt(s, liveAfter, ensuresVars);
        const iterSrc = aliasSourceRoot(s.iterable, typeDecls);
        let loopIn = cur;
        for (let idx = 0; idx < s.names.length; idx++) {
          const n = s.names[idx]!;
          const ty = s.nameTypes[idx];
          if (ty && isMutableRefTy(ty, typeDecls)) {
            if (iterSrc && loopIn.map.has(iterSrc)) {
              loopIn = { map: bindCopyGroup(loopIn.map, n, iterSrc, loopIn.nextId), nextId: loopIn.nextId + 1 };
            } else {
              loopIn = { map: bindFreshGroup(loopIn.map, n, loopIn.nextId), nextId: loopIn.nextId + 1 };
            }
          }
        }
        for (let iter = 0; iter < 16; iter++) {
          const dummyOut: LiveAliasConflict[] = [];
          const bodyOut = checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, typeDecls, fnName, dummyOut);
          const merged = joinAliasStates([loopIn, bodyOut]);
          if (aliasMapsEqual(merged.map, loopIn.map)) break;
          loopIn = merged;
        }
        checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, typeDecls, fnName, out);
        cur = loopIn;
        break;
      }
      default:
        break;
    }
  }
  return cur;
}

function checkFunctionAliases(fn: TFunction, fnLabel: string, typeDecls: TypeDeclInfo[], out: LiveAliasConflict[]): void {
  let state: AliasState = { map: new Map(), nextId: 1 };
  const paramNames = new Set<string>();
  for (const p of fn.params) {
    paramNames.add(p.name);
    if (isMutableRefTy(p.ty, typeDecls)) {
      state = { map: bindFreshGroup(state.map, p.name, state.nextId), nextId: state.nextId + 1 };
    }
  }
  // In Dafny/Lean, parameter mentions in `//@ ensures` refer to the entry
  // (pre-state) parameter value (e.g., `swap.ts`: `\result[i] === arr[j]`),
  // not a post-mutation executable read of `arr`. Keep only non-parameter
  // variables from `ensures` (if any) in `ensuresVars`.
  const ensuresVars = new Set<string>();
  for (const e of fn.ensures) {
    for (const v of freeVarsExpr(e)) {
      if (!paramNames.has(v)) ensuresVars.add(v);
    }
  }
  checkStmts(fn.body, state, ensuresVars, ensuresVars, typeDecls, fnLabel, out);
}

/** Check all functions and class methods in `mod` for live-alias mutations. */
export function checkModuleLiveAliases(mod: TModule): LiveAliasConflict[] {
  const out: LiveAliasConflict[] = [];
  for (const fn of mod.functions) {
    checkFunctionAliases(fn, fn.name, mod.typeDecls, out);
  }
  for (const cls of mod.classes ?? []) {
    for (const m of cls.methods) {
      checkFunctionAliases(m, `${cls.name}.${m.name}`, mod.typeDecls, out);
    }
  }
  return out;
}

/** Reject a module if any function mutates a mutable-ref binding while an alias is still live. */
export function assertNoLiveAliasMutations(mod: TModule): TModule {
  const conflicts = checkModuleLiveAliases(mod);
  if (conflicts.length > 0) {
    throw new Error(conflicts[0]!.detail);
  }
  return mod;
}
