import MicroCFTA.SourceEqualityDemandTargetComplete
import MicroCFTA.SourceEqualityClassEdits

/-!
# Original physical equality-class target construction

The target at one original path uses every other path in ascending class
order. Coherent nontrivial classes derive proper nonempty operand paths.
Actual demanded construction retains each equality-satisfying subterm.
-/
namespace MicroCFTA.SourceEqualityClassTarget
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget
open SourceEqualityClassEdits SourceEqualityDemandTargetComplete
open EqualityNormalize
open InternedGuardedLanguage (meaning)

/-- The actual source target uses the ordered class paths other than its own path. -/
def operandPaths (paths : Class) (selected : Path) : List (List Int) :=
  (EqualityNarrowing.others paths selected).map (List.map Int.ofNat)

/-- Every nontrivial original class has a nonempty source target operand list. -/
theorem operandPaths_nonempty (paths : Class) (active : Nontrivial paths) (selected : Path) : operandPaths paths selected ≠ [] := by
  intro absent
  exact EqualityNarrowing.others_nonempty paths active selected (List.map_eq_nil_iff.mp absent)

/-- A coherent nontrivial physical class derives every proper operand path. -/
theorem operandPaths_nonroot (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : Nontrivial record.paths) (selected : Path) : ∀ path ∈ operandPaths record.paths selected, path ≠ [] := by
  intro path member empty
  obtain ⟨original, included, same⟩ := List.mem_map.mp member
  cases same
  exact supported_nonroot record.paths (coherent_supported record coherent) active original (List.mem_filter.mp included).1
    (List.map_eq_nil_iff.mp empty)

/-- Actual target construction at an original class path retains every equality-satisfying selected subterm. -/
theorem target_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard)) (target : Value Symbol Guard)
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before target after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : ClassSat (.node symbol terms) record.paths) (selected : (Term.node symbol terms).atPath path = some part) :
    meaning holds ambient target part := by
  apply trace.included ready available closed (operandPaths_nonempty record.paths active path) (operandPaths_nonroot record coherent active path)
    holds ambient clearTrue topTrue conjoined symbol terms part accepted
  intro other included
  change other ∈ (EqualityNarrowing.others record.paths path).map (List.map Int.ofNat) at included
  obtain ⟨original, originalIn, same⟩ := List.mem_map.mp included
  cases same
  obtain ⟨common, selectedAt, otherAt⟩ := class_pair_equal (.node symbol terms) record.paths active satisfied path original member (List.mem_filter.mp originalIn).1
  have samePart := Option.some.inj (selectedAt.symm.trans selected)
  subst common
  simpa only [SourceEqualitySelectedRequired.lookup_natural] using otherAt

/-- Original class paths derive finite demanded targets with captured availability and no loss of class-satisfying terms. -/
theorem target_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base values) (closed : ClosedValues values)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before) (ranges : TargetRanges emptyGuard conjoin clear top values (operandPaths record.paths path) before)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ target after, Target emptyGuard conjoin clear top values (operandPaths record.paths path) before target after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧ Available after.machine.heap target ∧ target.free = [] ∧
      ∀ symbol terms part, All₂ (meaning holds ambient) values terms → ClassSat (.node symbol terms) record.paths →
        (Term.node symbol terms).atPath path = some part → meaning holds ambient target part := by
  have available : Values before.machine.heap values := fun value member => retained.available value (known value member)
  obtain ⟨target, after, trace, finalReady, keeps, resident, resultClosed⟩ :=
    SourceEqualityDemandTargetComplete.complete emptyGuard conjoin clear top values (operandPaths record.paths path) before ready ranges available closed
  exact ⟨target, after, trace, finalReady, retained.trans keeps, resident, resultClosed,
    target_included emptyGuard conjoin clear top record coherent active path member values target trace ready available closed holds ambient clearTrue topTrue conjoined⟩

end MicroCFTA.SourceEqualityClassTarget
