import MicroCFTA.SourceEqualitySharedClassEdits
import MicroCFTA.SourceEqualityEmptyPropagation

/-!
# Source class right fold with fresh class-local closures

The tail returns the current forest and actual native state. The next
class captures that forest and starts unforced target slots. A single
literal empty propagation follows the complete fold, as in the source.
-/
namespace MicroCFTA.SourceEqualityClassFoldGraph
open InternedConstructorTemplates SourceEqualityNativeScoped
open SourceEqualitySharedTargetState SourceEqualitySharedEditGraph

/-- The fold retains the actual constructor heap, domain cache, and both native memo tables. -/
abbrev NativeState (width : Nat) (Symbol Guard : Type) := SourceRecursiveIntersectionThunks.State width Symbol Guard

/-- Source class edit pairs retain original signed paths and natural closure tokens. -/
def edits (record : SourceEqualityClassOrder.Record) : SourceEqualityEdits.Edits EqualityNormalize.Path :=
  SourceEqualityEdits.build (SourceEqualityClassEdits.edits record.paths id)

/-- One class captures its current forest and starts fresh unforced target slots. -/
inductive Class [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) :
    List (Value Symbol Guard) → NativeState width Symbol Guard → List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | edit (actual : EditList emptyGuard conjoin clear top record values (edits record) values (initial before) results shared) :
      Class emptyGuard conjoin clear top record values before results shared.native

/-- Execute the source right fold; each class captures the forest returned by the completed tail. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → NativeState width Symbol Guard →
      List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | nil : Fold emptyGuard conjoin clear top [] values before values before
  | cons (tail : Fold emptyGuard conjoin clear top records values before middle next)
      (head : Class emptyGuard conjoin clear top record middle next results after) :
      Fold emptyGuard conjoin clear top (record :: records) values before results after

/-- The source applies literal empty propagation only after the entire class fold. -/
inductive Pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → NativeState width Symbol Guard →
      List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | done (fold : Fold emptyGuard conjoin clear top records values before results after) :
      Pass emptyGuard conjoin clear top records values before (EqualityLeafProjectionRuntimeEmpty.propagate results) after

/-- Only actual reached leaf prefixes of a fresh class require target and native word checks. -/
def ClassRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Prop :=
  SourceEqualitySharedEditRanges.ListRanges emptyGuard conjoin clear top record values (edits record) values (initial before)

/-- Every next class range plan refers to an actual completed tail forest and native state. -/
inductive Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard) :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | nil : Ranges emptyGuard conjoin clear top [] values before
  | cons (tail : Ranges emptyGuard conjoin clear top records values before)
      (head : ∀ middle next, Fold emptyGuard conjoin clear top records values before middle next → ClassRanges emptyGuard conjoin clear top record middle next) :
      Ranges emptyGuard conjoin clear top (record :: records) values before

end MicroCFTA.SourceEqualityClassFoldGraph
