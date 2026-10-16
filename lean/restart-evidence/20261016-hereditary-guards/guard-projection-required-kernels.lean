import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProjection
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardRequired
import MicroCFTA.SourceEqualityProjectionComplete

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 2000000
set_option format.width 200

namespace GuardProjectionRequiredKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Constraint" => SourceSymbolicIndex.Constraint
variable {Symbol Formula : Type} [DecidableEq (EdgeKey Symbol (Constraint Formula))]

/-- Initial finite ordinary inputs construct both actual operations at the same intermediate heap. -/
theorem projection_then_required (path : List Int) (required : List (List Int))
    (values : List (Value Symbol (Constraint Formula))) (before : State Symbol (Constraint Formula))
    (semantic : SemanticReady before) (available : Values before values)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) :
    ∃ projected middle results after,
      SourceEqualityProjectionGraph.Forest path values before projected middle ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel required [projected] middle) results after ∧
      SourceEqualityRequiredCache.Keeps before after ∧ SemanticReady after ∧ Values after results ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
        (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.childrenLimits values) projected ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
        (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.childrenLimits values) results := by
  have facts := semantic.ready.semantic.1.normal.facts
  have closed : MergedColdReaderClosedInputs.ClosedValues values := fun value member =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value (available value member)
      (domain.member value member)
  obtain ⟨projected, middle, projection, first, middleSemantic, projectedAvailable, _free⟩ :=
    SourceEqualityProjectionComplete.forest_complete path values before semantic available closed
  have projectedBound := SourceCurrentAllocatedFiniteOrdinaryGuardProjection.forest projection semantic available
    (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.children_self values domain)
  have originals : Values middle [projected] := by
    intro value member
    simpa only [List.mem_singleton.mp member] using projectedAvailable
  have originalDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children [projected] :=
    .cons (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.domain projected projectedBound) .nil
  have originalClosed : MergedColdReaderClosedInputs.ClosedValues [projected] := fun value member =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed middle middleSemantic.ready.semantic.1.normal.facts.coherent value
      (originals value member) (originalDomain.member value member)
  obtain ⟨results, after, _keeps, _available, _closed, stable⟩ :=
    SourceEqualityRequiredExecution.requireAll_complete required [projected] middle middleSemantic.ready originals originalClosed
  obtain ⟨fuel, readFuel, done⟩ := stable
  have execution := done fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel required
    [projected] results middle after execution middleSemantic originals originalDomain
  have resultBound := SourceCurrentAllocatedFiniteOrdinaryGuardRequired.requireAll_done fuel readFuel required
    [projected] results middle after execution middleSemantic originals _ ⟨projectedBound, True.intro⟩
  exact ⟨projected, middle, results, after, projection, ⟨fuel, readFuel, done⟩,
    first.trans physical.1, physical.2.1, physical.2.2.1, projectedBound, resultBound⟩

end GuardProjectionRequiredKernels
#print axioms GuardProjectionRequiredKernels.projection_then_required
#check @GuardProjectionRequiredKernels.projection_then_required
