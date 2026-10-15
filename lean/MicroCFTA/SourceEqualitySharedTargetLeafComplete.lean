import MicroCFTA.SourceEqualitySharedTargetLeaf

/-!
# Finite shared target leaves from actual demand-prefix checks

A returned target slot requires no construction bound. A first force uses
the actual demanded target ranges. The leaf word check follows that force
at its literal returned native state.
-/
namespace MicroCFTA.SourceEqualitySharedTargetLeafComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualitySharedTargetState SourceEqualitySharedTargetForce SourceEqualitySharedTargetLeaf

/-- A native leaf checks words only after the actual shared target force. -/
structure LeafRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) (input : Value Symbol Guard)
    (before : State width Symbol Guard) : Prop where
  force : ForceRanges emptyGuard conjoin clear top record values path before
  step : ∀ target middle, Force emptyGuard conjoin clear top record values path before target middle →
    SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) middle.native

/-- Local first-force progress and idle native progress derive complete shared target leaves. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
    (known : Values base values) (closed : ClosedValues values) (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (input : Value Symbol Guard) (before : State width Symbol Guard) (ready : Ready emptyGuard conjoin clear top record values base before)
    (ranges : LeafRanges emptyGuard conjoin clear top record values path input before)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = []) :
    ∃ result after, Leaf emptyGuard conjoin clear top record values path input before result after ∧
      Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Retains before after := by
  obtain ⟨target, middle, forced, middleReady, keeps, targetAvailable, targetClosed, _⟩ := SourceEqualitySharedTargetForce.complete
    emptyGuard conjoin clear top record values base known closed path member before ready ranges.force
  obtain ⟨result, native, step, _⟩ := SourceEqualityNativeScoped.complete emptyGuard conjoin middle.native middleReady.native
    target input targetAvailable (keeps.available input available) targetClosed inputClosed (ranges.step target middle forced)
    (fun _ _ => true) (fun _ _ _ => rfl)
  have trace : Leaf emptyGuard conjoin clear top record values path input before result (advance middle native) := .apply forced step
  exact ⟨result, _, trace, trace.effects ready known closed member available inputClosed⟩

end MicroCFTA.SourceEqualitySharedTargetLeafComplete
