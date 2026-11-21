/**
 * TypeDecls — declaration lookup over a module's type declarations
 * (DESIGN_LS_IN_LS.md §5.2).
 *
 * One home for the lookup idioms formerly re-spelled at each use site.
 * Three name semantics exist, and call sites deliberately differ:
 *   - exact:  `declOf` — the name as written;
 *   - dotted: `declOfDotted` — exact, else the last dotted segment
 *     (`Agent.Info` matches `//@ declare-type Info`);
 *   - sliced: `declOfTy`/`tyBaseName` — generic arguments stripped
 *     (`Foo<Bar>` looks up `Foo`).
 * Preserve a site's semantics when changing its lookup; do not "upgrade"
 * an exact site to dotted or sliced in passing.
 */

import type { Ty } from "./typedir.js";
import type { TypeDeclInfo } from "./types.js";

export type TypeDecls = readonly TypeDeclInfo[];

/** `Foo<Bar>` → `Foo`. The single home of the generic-base slice; §5.1
 *  (structured generic args) retires it. */
export function tyBaseName(name: string): string {
  return name.includes("<") ? name.slice(0, name.indexOf("<")) : name;
}

/** Declaration by exact name. With duplicate names this is the first. */
export function declOf(decls: TypeDecls, name: string): TypeDeclInfo | undefined {
  //@ ensures \result !== undefined ==> \result.name === name && decls.includes(\result)
  //@ ensures \result === undefined ==> forall(d, decls.includes(d) ==> d.name !== name)
  return decls.find(d => d.name === name);
}

/** Declaration by exact name, restricted to the given kinds. */
export function declOfKind(decls: TypeDecls, name: string,
    ...kinds: TypeDeclInfo["kind"][]): TypeDeclInfo | undefined {
  //@ ensures \result !== undefined ==> \result.name === name && kinds.includes(\result.kind) && decls.includes(\result)
  //@ ensures \result === undefined && namesUnique(decls) ==> forall(d, decls.includes(d) && d.name === name ==> !kinds.includes(d.kind))
  const d = declOf(decls, name);
  return d && kinds.includes(d.kind) ? d : undefined;
}

/** Declaration by exact name, falling back to the last dotted segment. */
export function declOfDotted(decls: TypeDecls, name: string): TypeDeclInfo | undefined {
  //@ ensures declOf(decls, name) !== undefined ==> \result === declOf(decls, name)
  //@ ensures \result !== undefined ==> decls.includes(\result) && (\result.name === name || (name.lastIndexOf(".") >= 0 && \result.name === name.slice(name.lastIndexOf(".") + 1)))
  //@ ensures \result === undefined ==> forall(d, decls.includes(d) ==> d.name !== name && (name.lastIndexOf(".") < 0 || d.name !== name.slice(name.lastIndexOf(".") + 1)))
  const direct = declOf(decls, name);
  if (direct) return direct;
  const dotIdx = name.lastIndexOf(".");
  if (dotIdx >= 0) return declOf(decls, name.slice(dotIdx + 1));
  return undefined;
}

/** Declaration for a user-typed value: generic-base sliced, exact match.
 *  Undefined for non-user types. */
export function declOfTy(decls: TypeDecls, ty: Ty): TypeDeclInfo | undefined {
  //@ ensures ty.kind !== "user" ==> \result === undefined
  //@ ensures \result !== undefined ==> ty.kind === "user" && \result.name === tyBaseName(ty.name) && decls.includes(\result)
  //@ ensures ty.kind === "user" && \result === undefined ==> forall(d, decls.includes(d) ==> d.name !== tyBaseName(ty.name))
  return ty.kind === "user" ? declOf(decls, tyBaseName(ty.name)) : undefined;
}

/** The discriminated-union declaration of a user-typed value, if any. */
export function unionDeclOfTy(decls: TypeDecls, ty: Ty): TypeDeclInfo | undefined {
  //@ ensures \result !== undefined ==> \result.kind === "discriminated-union" && ty.kind === "user" && \result.name === tyBaseName(ty.name) && decls.includes(\result)
  //@ ensures ty.kind === "user" && \result === undefined && namesUnique(decls) ==> forall(d, decls.includes(d) && d.name === tyBaseName(ty.name) ==> d.kind !== "discriminated-union")
  const d = declOfTy(decls, ty);
  return d?.kind === "discriminated-union" ? d : undefined;
}

/** The discriminant field name of a user-typed value that is a
 *  discriminated union. */
export function discriminantOf(decls: TypeDecls, ty: Ty): string | undefined {
  //@ ensures \result !== undefined ==> ty.kind === "user" && exists(d, decls.includes(d) && d.kind === "discriminated-union" && d.name === tyBaseName(ty.name) && d.discriminant === \result)
  return unionDeclOfTy(decls, ty)?.discriminant;
}

/** Reverse lookup: the union declaration owning a variant (discriminated
 *  union) or literal value (string union) of this name. */
export function declWithVariant(decls: TypeDecls, ctorOrValue: string): TypeDeclInfo | undefined {
  //@ ensures \result !== undefined ==> decls.includes(\result) && ownsVariant(\result, ctorOrValue)
  //@ ensures \result === undefined ==> forall(d, decls.includes(d) ==> !ownsVariant(d, ctorOrValue))
  return decls.find(d => (d.kind === "discriminated-union" || d.kind === "string-union") &&
    ((d.variants?.some(v => v.name === ctorOrValue)) || (d.values?.includes(ctorOrValue) ?? false)));
}

// Specification helpers for the lookup contracts above (DESIGN_LS_IN_LS.md
// §8.1). Nothing in the compiler calls them; lsc translates them with the
// module so the contracts can name them.

/** Spec: no two declarations share a name. Extract does not guarantee this:
 *  most of its push sites skip the duplicate check. `declOf` returns the
 *  first match, so a lookup that filters that match (`declOfKind`,
 *  `unionDeclOfTy`) can return `undefined` while a later same-named
 *  declaration would have passed the filter. Their completeness contracts
 *  hold under this premise. */
export function namesUnique(decls: TypeDecls): boolean {
  if (decls.length === 0) return true;
  const rest = decls.slice(1);
  return !rest.some(d => d.name === decls[0].name) && namesUnique(rest);
}

/** Spec: `d` is a union declaration that has `ctorOrValue` as a
 *  discriminated-union variant name or a string-union literal. */
export function ownsVariant(d: TypeDeclInfo, ctorOrValue: string): boolean {
  if (d.kind !== "discriminated-union" && d.kind !== "string-union") return false;
  const inVariants = d.variants !== undefined && d.variants.some(v => v.name === ctorOrValue);
  const inValues = d.values !== undefined && d.values.includes(ctorOrValue);
  return inVariants || inValues;
}
