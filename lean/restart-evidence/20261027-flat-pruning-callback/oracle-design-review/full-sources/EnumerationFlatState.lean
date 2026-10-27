import MicroCFTA.FlatUnionFindStable
import MicroCFTA.EnumerationResultRelation

/-!
# Enumeration core state with direct-parent union-find

Only the forest representation changes. Values, obligations and ancestry use
the existing core types. Native expandable and waiting indexes remain outside
this six-field projection. The earlier state and all its proofs remain intact.
-/

namespace MicroCFTA.EnumerationFlatState

open EnumerationState (UVarValue RecursionKey Error Suspended)
open Fragments (Fragment)

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- The existing enumeration core with the current union-find representation. -/
structure State (Symbol Guard : Type) where
  /-- The next equality-variable identifier. -/
  counter : Nat
  /-- Direct parents and complete root member sets. -/
  representatives : FlatUnionFind.Forest
  /-- Values indexed by their raw variable identifiers. -/
  values : List (UVarValue Symbol)
  /-- Residual guards and the fragments to which they apply. -/
  obligations : List (Guard × Fragment Symbol)
  /-- Recursion keys retained at each raw variable. -/
  recursionAncestry : Nat → List RecursionKey
  /-- Recursion keys of the current expansion. -/
  expansionAncestry : List RecursionKey

/-- Core state correspondence retains every field except the forest shape. -/
structure Related (flat : State Symbol Guard) (earlier : EnumerationState.State Symbol Guard) : Prop where
  /-- The current direct-parent representation is valid. -/
  valid : FlatUnionFind.Valid flat.representatives
  /-- Every variable has the same representative and stored class size. -/
  representatives : FlatUnionFind.Represents flat.representatives earlier.representatives
  /-- Both states use the same fresh identifier. -/
  counter : flat.counter = earlier.counter
  /-- All raw value slots are equal. -/
  values : flat.values = earlier.values
  /-- All residual obligations are equal and ordered alike. -/
  obligations : flat.obligations = earlier.obligations
  /-- Both per-variable ancestry functions are equal. -/
  recursionAncestry : flat.recursionAncestry = earlier.recursionAncestry
  /-- Both expansion ancestry lists are equal. -/
  expansionAncestry : flat.expansionAncestry = earlier.expansionAncestry

/-- The root starts at variable zero with a singleton direct-parent forest. -/
def initial (root : Nat) : State Symbol Guard :=
  ⟨1, FlatUnionFind.withInitialValues [0], [.unenumerated (some root) []], [], fun _ => [], []⟩

/-- Initialization relates the complete six-field core states. -/
theorem initial_related (root : Nat) :
    Related (initial (Symbol := Symbol) (Guard := Guard) root) (EnumerationState.initial root) :=
  ⟨FlatUnionFind.initial_valid [0], FlatUnionFind.initial_represents [0], rfl, rfl, rfl, rfl, rfl⟩

/-- Change only the related forests and retain all other core fields. -/
theorem related_forests (related : Related flat earlier)
    (valid : FlatUnionFind.Valid newFlat) (forests : FlatUnionFind.Represents newFlat newEarlier) :
    Related {flat with representatives := newFlat} {earlier with representatives := newEarlier} :=
  ⟨valid, forests, related.counter, related.values, related.obligations,
    related.recursionAncestry, related.expansionAncestry⟩

/-- Core actions keep ordered successes, explicit errors and branch-local state. -/
abbrev Action (Symbol Guard α : Type) := StateT (State Symbol Guard) (ExceptT Error List) α

/-- Reject the current alternative. -/
def reject : Action Symbol Guard α := fun _ => []

/-- Retain an explicit core error. -/
def failure (error : Error) : Action Symbol Guard α := fun _ => [.error error]

/-- Retain a branch exactly when the guard is true. -/
def require (condition : Bool) : Action Symbol Guard Unit :=
  if condition then pure () else reject

/-- Read the direct representative and retain the input forest. -/
def representative (uv : Nat) : Action Symbol Guard Nat := fun before =>
  let found := FlatUnionFind.find before.representatives uv
  [.ok (found.1, {before with representatives := found.2})]

/-- Merge the requested classes before any raw-slot assimilation. -/
def unionVariables (left right : Nat) : Action Symbol Guard Unit := fun before =>
  [.ok ((), {before with representatives := FlatUnionFind.union before.representatives left right})]

/-- Write the supplied raw variable rather than its representative. -/
def setValue (uv : Nat) (value : UVarValue Symbol) : Action Symbol Guard Unit :=
  modify fun state => {state with values := state.values.set uv value}

/-- Read a raw slot and retain an explicit invalid-slot error. -/
def rawValue (uv : Nat) : Action Symbol Guard (UVarValue Symbol) := fun before =>
  match before.values[uv]? with
  | none => [.error .invalidSlot]
  | some value => [.ok (value, before)]

/-- Read the slot at the current direct representative. -/
def getValue (uv : Nat) : Action Symbol Guard (UVarValue Symbol) := do
  rawValue (← representative uv)

/-- Give one variable the current expansion ancestry in the core projection. -/
def inheritAncestry (uv : Nat) : Action Symbol Guard Unit :=
  modify fun state => {state with recursionAncestry := (fun other =>
    if other = uv then (state.expansionAncestry ++ state.recursionAncestry uv).eraseDups
    else state.recursionAncestry other)}

/-- Allocate one raw slot and retain the core ancestry update. -/
def allocate (node : Option Nat) : Action Symbol Guard Nat := do
  let state ← get
  let uv := state.counter
  set {state with counter := uv + 1, values := state.values ++ [UVarValue.unenumerated node []]}
  inheritAncestry uv
  pure uv

end MicroCFTA.EnumerationFlatState
