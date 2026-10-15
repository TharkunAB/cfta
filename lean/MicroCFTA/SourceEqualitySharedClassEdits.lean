import MicroCFTA.SourceEqualitySharedEditAPI
import MicroCFTA.SourceEqualitySharedEditLanguage
import MicroCFTA.SourceEqualityClassEdits

/-!
# Original class paths through shared simultaneous edits

The signed compiler stores each original natural path as its leaf token.
Targets remain unforced until their first actual leaf visit. Completed
class edits narrow the input language and retain all class-satisfying terms.
-/
namespace MicroCFTA.SourceEqualitySharedClassEdits
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualitySharedTargetState SourceEqualitySharedEditGraph
open SourceEqualityEdits SourceEqualitySharedEditRanges SourceEqualitySharedEditEffects
open SourceEqualityClassEdits
open InternedGuardedLanguage (meaning)

/-- Compilation retains only original paths of the captured source class. -/
theorem compiled_allowed (record : SourceEqualityClassOrder.Record) : Allowed record (build (edits record.paths id)) := by
  apply build_all
  intro path token member
  obtain ⟨original, included, same⟩ := List.mem_map.mp member
  cases same
  exact included

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
variable (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals) (closed : ClosedValues originals)
variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
variable (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
variable (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))

include coherent active known closed clearTrue topTrue conjoined

/-- Shared class edits narrow the original forest and preserve every accepted class-satisfying term. -/
theorem language {before results after}
    (trace : EditList (width := width) emptyGuard conjoin clear top record originals (build (edits record.paths id)) originals before results after)
    (ready : Ready emptyGuard conjoin clear top record originals base before) (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) originals terms) ∧
      (EqualityNormalize.ClassSat (.node symbol terms) record.paths → All₂ (meaning holds ambient) originals terms → All₂ (meaning holds ambient) results terms) := by
  have supported := coherent_supported record coherent
  have matched : SourceEqualityEditAPI.ListCondition (fun path part => (Term.node symbol terms).atPath path = some part)
      (build (edits record.paths id)) terms := by
    apply (SourceEqualityEditCompiledPaths.list_condition_exact _ _ (edits_disjoint _ supported id)
      (edits_nonroot _ (supported_nonroot _ supported active) id) symbol terms).mpr
    exact (conditions_exact _ record.paths id (.node symbol terms)).mpr (fun _ _ _ selected => selected)
  have bounds := SourceEqualitySharedEditLanguage.list emptyGuard conjoin clear top record originals base known closed holds ambient
    (.node symbol terms) symbol terms coherent active clearTrue topTrue conjoined rfl trace
    (build_valid _) (compiled_allowed record) ready (fun value member => ready.captured.available value (known value member)) closed terms
  exact ⟨bounds.1, fun satisfied accepted => bounds.2 accepted satisfied matched accepted⟩

/-- Accepted terms that satisfy the original class have identical before and after membership. -/
theorem exact_when_satisfied {before results after}
    (trace : EditList (width := width) emptyGuard conjoin clear top record originals (build (edits record.paths id)) originals before results after)
    (ready : Ready emptyGuard conjoin clear top record originals base before) (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) originals terms := by
  have bounds := language emptyGuard conjoin clear top record coherent active originals base known closed holds ambient clearTrue topTrue conjoined trace ready symbol terms
  exact ⟨bounds.1, bounds.2 satisfied⟩

/-- Local first-demand checks derive finite class execution, retained target slots, and independent language bounds. -/
theorem complete (before : SharedState width Symbol Guard) (ready : Ready emptyGuard conjoin clear top record originals base before)
    (ranges : ListRanges emptyGuard conjoin clear top record originals (build (edits record.paths id)) originals before) :
    ∃ results after, EditList emptyGuard conjoin clear top record originals (build (edits record.paths id)) originals before results after ∧
      Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ SourceEqualitySharedTargetForce.Retains before after ∧
      SourceEqualitySharedEditWorkerComplete.StableRun
        (fun e p h c n => SourceEqualitySharedEditWorker.editAll emptyGuard conjoin clear top record originals e p h c n (edits record.paths id) originals before) results after ∧
      ∀ symbol terms, (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) originals terms) ∧
        (EqualityNormalize.ClassSat (.node symbol terms) record.paths → All₂ (meaning holds ambient) originals terms → All₂ (meaning holds ambient) results terms) := by
  obtain ⟨results, after, trace, finalReady, keeps, available, resultClosed, retained, stable⟩ :=
    SourceEqualitySharedEditAPI.list_complete emptyGuard conjoin clear top record originals base known closed ranges (compiled_allowed record) ready
      (fun value member => ready.captured.available value (known value member)) closed
  exact ⟨results, after, trace, finalReady, keeps, available, resultClosed, retained, stable,
    fun symbol terms => language emptyGuard conjoin clear top record coherent active originals base known closed holds ambient clearTrue topTrue conjoined trace ready symbol terms⟩

end MicroCFTA.SourceEqualitySharedClassEdits
