import MicroCFTA.SourceCurrentMemoSharedEditWorker
import MicroCFTA.SourceCurrentMemoClassPass

/-!
# Executable class folds with the actual completed merge table

Each class captures the forest, native state, and merge table returned by
its tail. Only the class target slots start empty. Failed classes retain
their captured forest and the complete shared worker observation.
Literal empty propagation follows the completed fold once.
-/
namespace MicroCFTA.SourceCurrentMemoClassWorker
open InternedConstructorTemplates SourceCurrentMemoClassPass
open SourceCurrentMemoMergeGraph (Memo)
local notation "Native" => SourceRecursiveIntersectionThunks.State

/-- Completed classes return both states; failures retain the captured class and full shared observation. -/
inductive Outcome (width : Nat) (Symbol Guard A : Type) : Type 1 where
  | done (value : A) (native : Native width Symbol Guard) (memo : Memo Symbol Guard)
  | incomplete (record : SourceEqualityClassOrder.Record) (captured : List (Value Symbol Guard))
      (observation : SourceCurrentMemoSharedLeafWorker.Outcome width Symbol Guard (List (Value Symbol Guard)))

/-- A completed tail passes both returned states to its continuation. -/
def Outcome.bind (first : Outcome width Symbol Guard A)
    (next : A → Native width Symbol Guard → Memo Symbol Guard → Outcome width Symbol Guard B) : Outcome width Symbol Guard B :=
  match first with
  | .done value native memo => next value native memo
  | .incomplete record captured observation => .incomplete record captured observation

/-- Execute the actual class trie over fresh slots and the retained native state and merge table. -/
def classEdit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (e p h w c n : Nat) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Native width Symbol Guard) (memo : Memo Symbol Guard) : Outcome width Symbol Guard (List (Value Symbol Guard)) :=
  match SourceCurrentMemoSharedEditWorker.editAll emptyGuard conjoin clear top record values e p h w c n
      (SourceEqualityClassEdits.edits record.paths id) values (SourceCurrentMemoSharedTargetState.initial before memo) with
  | .done results after => .done results after.native after.memo
  | other => .incomplete record values other

/-- The source right fold retains the forest, native state, and merge table returned by every tail. -/
def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (e p h w c n : Nat) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Native width Symbol Guard → Memo Symbol Guard →
      Outcome width Symbol Guard (List (Value Symbol Guard))
  | [], values, before, memo => .done values before memo
  | record :: records, values, before, memo =>
      (fold emptyGuard conjoin clear top e p h w c n records values before memo).bind fun current native saved =>
        classEdit emptyGuard conjoin clear top e p h w c n record current native saved

/-- Propagate literal empty children once after the entire class fold. -/
def pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (e p h w c n : Nat) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Native width Symbol Guard) (memo : Memo Symbol Guard) : Outcome width Symbol Guard (List (Value Symbol Guard)) :=
  (fold emptyGuard conjoin clear top e p h w c n records values before memo).bind fun results after saved =>
    .done (EqualityLeafProjectionRuntimeEmpty.propagate results) after saved

end MicroCFTA.SourceCurrentMemoClassWorker
