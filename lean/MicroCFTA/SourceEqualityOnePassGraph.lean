import MicroCFTA.SourceEqualitySelectedClassFold

/-!
# Guarded native one-pass equality graph

Source prechecks run first. Unchanged and contradiction returns bypass
selection and narrowing. The live branch retains actual selected/required
receipts, the native right fold, and one final empty propagation.
-/
namespace MicroCFTA.SourceEqualityOnePassGraph
open InternedConstructorTemplates SourceEqualityClassFoldGraph
open SourceEqualityPrecheck (Branch)

/-- A checked one-pass graph retains every immediate source return and actual live-stage receipt. -/
inductive Graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (checked : Except String Branch) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
    Except String (List (Value Symbol Guard)) → NativeState width Symbol Guard → Prop where
  | error (actual : checked = .error message) : Graph unconstrained emptyGuard conjoin clear top checked values before (.error message) before
  | unchanged (actual : checked = .ok .unchanged) : Graph unconstrained emptyGuard conjoin clear top checked values before (.ok values) before
  | emptyChildren (actual : checked = .ok .emptyChildren) :
      Graph unconstrained emptyGuard conjoin clear top checked values before (.ok (EqualityLeafProjectionRuntimeEmpty.erase values)) before
  | live (actual : checked = .ok (.classes records))
      (stages : SourceEqualitySelectedClassFold.Execution unconstrained emptyGuard conjoin clear top records values before queries middle required heap results after) :
      Graph unconstrained emptyGuard conjoin clear top checked values before (.ok results) after

/-- A one-pass execution uses the actual source guards and physical class order. -/
abbrev Execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (own inherited : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :=
  Graph unconstrained emptyGuard conjoin clear top (SourceEqualityPrecheck.precheck own inherited) values before

/-- Native word checks are required only in the live branch after actual selected/required stages. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (checked : Except String Branch) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Prop :=
  match checked with
  | .ok (.classes records) => ∀ queries middle required heap,
      SourceEqualitySelectedRequired.Execution unconstrained values (records.map SourceEqualityClassOrder.Record.paths)
        before.machine.heap queries middle required heap →
      SourceEqualityClassFoldGraph.Ranges emptyGuard conjoin clear top (SourceEqualitySelectedRecords.keep records queries) required
        (SourceEqualityNativeScoped.advanceHeap before heap)
  | _ => True

end MicroCFTA.SourceEqualityOnePassGraph
