import MicroCFTA.SourceEqualityNativeEditAPI
import MicroCFTA.SourceEqualityClassEdits

/-!
# Original physical class paths through scoped native edits

Coherent nontrivial source classes derive disjoint nonroot edit paths. Their
captured physical targets use actual native intersection leaves. All cache,
finite execution, and exact forest-language premises follow from scoped edits.
-/
namespace MicroCFTA.SourceEqualityNativeClassEdits
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityNativeEditGraph
open SourceEqualityEdits SourceEqualityNativeEditRanges
open SourceEqualityClassEdits
open InternedGuardedLanguage (meaning)

/-- Actual scoped native class edits have exact readback at the original natural class paths. -/
theorem class_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (target : EqualityNormalize.Path → Value Symbol Guard)
    (known : ∀ path ∈ record.paths, Available base (target path) ∧ (target path).free = [])
    {values before results after} (trace : EditList (width := width) emptyGuard conjoin (build (edits record.paths target)) values before results after)
    (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (symbol : Symbol) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
      ∀ path ∈ record.paths, ∀ part, (Term.node symbol terms).atPath path = some part → meaning holds ambient (target path) part := by
  have supported := coherent_supported record coherent
  have captured : ∀ path value, (path, value) ∈ edits record.paths target → Available base value ∧ value.free = [] := by
    intro path value member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact known original included
  rw [SourceEqualityNativeEditAPI.compiled_paths emptyGuard conjoin base holds ambient conjoined _
    (edits_disjoint _ supported target) (edits_nonroot _ (supported_nonroot _ supported active) target) captured
    trace retained ready available closed symbol terms, conditions_exact]

/-- Original class targets and actual-prefix word checks derive finite stable class edits and their exact path language. -/
theorem class_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (target : EqualityNormalize.Path → Value Symbol Guard)
    (known : ∀ path ∈ record.paths, Available base (target path) ∧ (target path).free = [])
    (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before) (ranges : ListRanges emptyGuard conjoin (build (edits record.paths target)) values before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, EditList emptyGuard conjoin (build (edits record.paths target)) values before results after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      SourceEqualityNativeEditWorkerComplete.StableRun
        (fun fuel readFuel nativeFuel => SourceEqualityNativeEditWorker.editAll emptyGuard conjoin fuel readFuel nativeFuel (edits record.paths target) values before) results after ∧
      ∀ symbol terms, All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
        ∀ path ∈ record.paths, ∀ part, (Term.node symbol terms).atPath path = some part → meaning holds ambient (target path) part := by
  have captured : ∀ path value, (path, value) ∈ edits record.paths target → Available base value ∧ value.free = [] := by
    intro path value member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact known original included
  obtain ⟨results, after, trace, finalReady, keeps, resultAvailable, resultClosed, stable, _⟩ :=
    SourceEqualityNativeEditAPI.compiled_complete emptyGuard conjoin base _ captured values before retained ready ranges available closed holds ambient conjoined
  exact ⟨results, after, trace, finalReady, keeps, resultAvailable, resultClosed, stable,
    fun symbol terms => class_exact emptyGuard conjoin base holds ambient conjoined record coherent active target known trace retained ready available closed symbol terms⟩

end MicroCFTA.SourceEqualityNativeClassEdits
