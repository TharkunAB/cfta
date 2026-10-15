import MicroCFTA.SourceEqualityPartialNodeRebuild
import MicroCFTA.SourceEqualityMuReconstruction

/-!
# Bounded outer partial reduction with actual source branches

The adapter bounds recursive traversal separately from six native stages.
It keeps EmptyNode, interned unions, actual Mu reconstruction, ordinary row
mapping, and the source Rec error. It records exhausted observations without
claiming that a sufficient traversal bound always exists. The outer Haskell
memo table and lazy scheduling remain outside this explicit execution.
-/
namespace MicroCFTA.SourceEqualityPartialWorker
open Cache InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- Unfinished outer execution retains the exact traversal, row, or pending-constructor observation. -/
inductive Observation (width : Nat) : Type 1 where
  | exhausted (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard) (state : NativeState width Symbol Guard)
  | rows (result : SourceEqualityInheritedRows.Result width (Observation width))
  | pending (key : InternedBinderProtocol.NodeKey) (state : NativeState width Symbol Guard)

/-- Complete outer answers retain the full native state used by the next source request. -/
abbrev Result (width : Nat) := SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) (Observation width)

/-- Execute one actual source branch with the supplied recursive callback. -/
noncomputable def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width)
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard)
    (before : NativeState width Symbol Guard) : Result width :=
  match value with
  | .empty => .done (.ok .empty) before
  | .reference _ => .done (.error "reducePartially: unexpected Rec") before
  | .union .. => .done (.ok value) before
  | .mu entry body depth ordinary =>
      match SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.machine.heap with
      | .done result heap => .done (.ok result) (advanceHeap before heap)
      | .pending key heap => .incomplete (.pending key (advanceHeap before heap))
  | .node entry edges depth free =>
      match SourceEqualityInheritedRows.walk call g e p h c n inherited edges before with
      | .done (.ok results) middle =>
          let built := SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle
          .done (.ok built.1) built.2
      | .done (.error message) middle => .done (.error message) middle
      | observation => .incomplete (.rows observation)

/-- Bounded recursion preserves each exact incomplete observation of a smaller source call. -/
noncomputable def run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (g e p h c n : Nat) : Nat → SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width
  | 0, inherited, value, before => .incomplete (.exhausted inherited value before)
  | fuel + 1, inherited, value, before => step (run g e p h c n fuel) g e p h c n inherited value before

/-- A zero traversal bound records its input and full current native state. -/
theorem exhausted [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard) (before : NativeState width Symbol Guard) :
    run g e p h c n 0 inherited value before = .incomplete (.exhausted inherited value before) := rfl

/-- Every positive traversal bound returns the source reference error at the original scope. -/
theorem reference_error [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (g e p h c n fuel : Nat) (inherited : SourceEqualityPrecheck.Constraint) (name : InternedBinderProtocol.Reference) (before : NativeState width Symbol Guard) :
    run g e p h c n (fuel + 1) inherited (.reference name) before = .done (.error "reducePartially: unexpected Rec") before := rfl

/-- The source empty branch makes no recursive request and changes no native state. -/
theorem empty_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (g e p h c n fuel : Nat) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :
    run g e p h c n (fuel + 1) inherited .empty before = .done (.ok .empty) before := rfl

/-- Interned source unions return their identical complete payload without traversing members. -/
theorem union_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (g e p h c n fuel : Nat) (inherited : SourceEqualityPrecheck.Constraint) (entry : Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : NativeState width Symbol Guard) :
    run g e p h c n (fuel + 1) inherited (.union entry members depth free) before = .done (.ok (.union entry members depth free)) before := rfl

end MicroCFTA.SourceEqualityPartialWorker
