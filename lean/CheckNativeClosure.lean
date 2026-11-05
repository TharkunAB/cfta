/-
Run with:
  nix-shell --run 'cd lean && lake env lean CheckNativeClosure.lean'

This command checks the types and values of five fixed declarations.
The limits are 4096 nodes, depth 128, and 16 universe parameters per declaration.
The node budget applies to both the type and the value.
The output contains binder scopes and dependency constraints.
A completed command can report CHECK_REJECTED. Inspect all five record statuses.
Checker soundness and native effect transport require separate proofs.
-/

import Lean

open Lean Elab Command

namespace NativeClosureCheck

private structure Spec where
  target : Name
  record : Name
  index : Nat

private structure BinderConstraint where
  id : Nat
  scope : List Nat
  direct : List Nat
  closure : List Nat

private structure Scan where
  nodes : Nat := 0
  levels : Nat := 0
  maxDepth : Nat := 0
  constantRefs : Nat := 0
  targetConstantRefs : Nat := 0
  expectedProjections : Nat := 0
  otherProjections : Nat := 0
  binders : List BinderConstraint := []

private def merge (xs ys : List Nat) : List Nat :=
  ys.foldl (fun acc n => if acc.contains n then acc else n :: acc) xs

private def tick (fuel : Nat) (s : Scan) : Except String Scan :=
  if s.nodes >= 4096 then .error "NODE_CAP"
  else .ok { s with nodes := s.nodes + 1, maxDepth := max s.maxDepth (129 - fuel) }

private def params : Nat → List Name → List Name → Except String (List Name)
  | _, [], acc => .ok acc
  | 0, _ :: _, _ => .error "PARAMETER_CAP"
  | k + 1, n :: ns, acc =>
    if acc.contains n then .error "DUPLICATE_PARAMETER" else params k ns (n :: acc)

private def lookupBound : List Nat → Nat → Option Nat
  | [], _ => none
  | n :: _, 0 => some n
  | _ :: ns, k + 1 => lookupBound ns k

private def binder (scope direct : List Nat) (s : Scan) : Except String (Scan × Nat) := do
  let mut closure := direct
  for i in direct do
    unless scope.contains i do throw "DIRECT_DEPENDENCY_OUTSIDE_SCOPE"
    let some prior := s.binders.find? (fun b => b.id == i)
      | throw "MISSING_DEPENDENCY_RECORD"
    closure := merge closure prior.closure
  unless closure.all scope.contains do throw "CLOSURE_OUTSIDE_SCOPE"
  let id := s.binders.length
  let row : BinderConstraint := ⟨id, scope, direct, closure⟩
  pure ({ s with binders := s.binders ++ [row] }, id)

private def level : Nat → List Name → Level → Scan → Except String Scan
  | 0, _, _, _ => .error "DEPTH_CAP"
  | k + 1, ps, u, s => do
    let s ← tick (k + 1) s
    let s := { s with levels := s.levels + 1 }
    match u with
    | .zero => pure s
    | .succ v => level k ps v s
    | .max a b | .imax a b => do
      let s ← level k ps a s
      level k ps b s
    | .param n => if ps.contains n then pure s else throw "UNBOUND_LEVEL_PARAMETER"
    | .mvar _ => throw "LEVEL_METAVARIABLE"

private def expr : Nat → Spec → List Name → List Nat → Expr → Scan →
    Except String (Scan × List Nat)
  | 0, _, _, _, _, _ => .error "DEPTH_CAP"
  | k + 1, spec, ps, scope, e, s => do
    let s ← tick (k + 1) s
    match e with
    | .bvar i =>
      match lookupBound scope i with
      | some id => pure (s, [id])
      | none => throw "LOOSE_BOUND_VARIABLE"
    | .fvar _ => throw "FREE_VARIABLE"
    | .mvar _ => throw "EXPRESSION_METAVARIABLE"
    | .sort u => do
      let s ← level k ps u s
      pure (s, [])
    | .const n us => do
      let s := { s with
        constantRefs := s.constantRefs + 1,
        targetConstantRefs := s.targetConstantRefs + (if n == spec.target then 1 else 0) }
      let s ← us.foldlM (fun s u => level k ps u s) s
      pure (s, [])
    | .app f a => do
      let (s, ds) ← expr k spec ps scope f s
      let (s, es) ← expr k spec ps scope a s
      pure (s, merge ds es)
    | .lam _ a b _ | .forallE _ a b _ => do
      let (s, ds) ← expr k spec ps scope a s
      let (s, id) ← binder scope ds s
      let (s, es) ← expr k spec ps (id :: scope) b s
      pure (s, merge ds (es.filter (fun n => n != id)))
    | .letE _ a v b _ => do
      let (s, ds) ← expr k spec ps scope a s
      let (s, es) ← expr k spec ps scope v s
      let direct := merge ds es
      let (s, id) ← binder scope direct s
      let (s, fs) ← expr k spec ps (id :: scope) b s
      pure (s, merge direct (fs.filter (fun n => n != id)))
    | .proj n i b => do
      let expected := n == spec.record && i == spec.index
      let s := { s with
        expectedProjections := s.expectedProjections + (if expected then 1 else 0),
        otherProjections := s.otherProjections + (if expected then 0 else 1) }
      expr k spec ps scope b s
    | .lit _ => throw "UNOPENED_LITERAL_CONTEXT"
    | .mdata _ _ => throw "UNOPENED_MDATA_CONTEXT"

private def binderJson (b : BinderConstraint) : Json := Json.mkObj [
  ("id", toJson b.id), ("scope", toJson b.scope),
  ("direct", toJson b.direct), ("closure", toJson b.closure),
  ("constraints_ok", toJson (b.direct.all b.scope.contains && b.closure.all b.scope.contains))]

private def check (spec : Spec) : DefinitionVal → Except String Json
  | .mk (.mk n ps rawType) rawValue _ _ _ => do
    unless n == spec.target do throw "CONSTRUCTOR_NAME_SLOT_MISMATCH"
    let ps ← params 16 ps []
    let (s, typeDependencies) ← expr 128 spec ps [] rawType {}
    unless typeDependencies.isEmpty do throw "TYPE_ROOT_DEPENDENCY"
    let typeNodes := s.nodes
    let (s, valueDependencies) ← expr 128 spec ps [] rawValue s
    unless valueDependencies.isEmpty do throw "VALUE_ROOT_DEPENDENCY"
    unless s.binders.all (fun b => b.direct.all b.scope.contains && b.closure.all b.scope.contains)
      do throw "BINDER_CONSTRAINT_FAILURE"
    pure <| Json.mkObj [
      ("target", toJson spec.target.toString), ("status", toJson "CONSTRUCTOR_CONSTRAINTS_CHECKED"),
      ("parameters", toJson ps.length), ("total_nodes", toJson s.nodes),
      ("type_nodes", toJson typeNodes), ("value_nodes", toJson (s.nodes - typeNodes)),
      ("level_nodes", toJson s.levels), ("max_depth", toJson s.maxDepth),
      ("constant_reference_count", toJson s.constantRefs),
      ("target_constant_reference_count", toJson s.targetConstantRefs),
      ("expected_projection_count", toJson s.expectedProjections),
      ("other_projection_count", toJson s.otherProjections),
      ("binder_constraints", toJson (s.binders.map binderJson))]

private def specs : List Spec := [
  ⟨``Pure.pure, ``Pure, 0⟩,
  ⟨``Applicative.toPure, ``Applicative, 1⟩,
  ⟨``Monad.toApplicative, ``Monad, 0⟩,
  ⟨``MonadState.modifyGet, ``MonadState, 2⟩,
  ⟨``MonadStateOf.modifyGet, ``MonadStateOf, 2⟩]

run_cmd do
  let env ← getEnv
  let mut rows : List Json := []
  for spec in specs do
    let some info := env.find? spec.target | throwError "MISSING_FIXED_TARGET"
    match info with
    | .defnInfo value =>
      match check spec value with
      | .ok row => rows := rows ++ [row]
      | .error code => rows := rows ++ [Json.mkObj [
          ("target", toJson spec.target.toString), ("status", toJson "CHECK_REJECTED"),
          ("code", toJson code)]]
    | _ => throwError "FIXED_TARGET_KIND_MISMATCH"
  let output := (Json.mkObj [("records", toJson rows)]).compress
  if output.utf8ByteSize + 1 > 8192 then throwError "OUTPUT_CAP"
  liftIO <| IO.println output

end NativeClosureCheck
