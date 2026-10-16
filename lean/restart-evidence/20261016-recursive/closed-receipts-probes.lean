import MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts

#print axioms MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.mu_node_law
#check MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.mu_node_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.input_finite
#check MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.input_finite
#print axioms MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.node_closed_exact
#check MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.node_closed_exact
#print axioms MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.node_meaning
#check MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.node_meaning
#print axioms MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.node_produced
#check MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.node_produced
#print axioms MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.source_models
#check MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.source_models

namespace MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.Probes
noncomputable section
open Language BinderLanguage InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

def emptyRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩

example (state : Checked width) : SourceEqualityNativeDemand.execute 1
    (.code (compileNode emptyRequest)) state = .done .empty state := by rfl

example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool) :
    NodeLaw view model ranked holds emptyRequest .empty := by
  constructor
  · intro _ _ _ _ accepted
    simp only [InternedGuardedLanguage.meaning] at accepted
  · intro _ _ _ _ _ _ _ _ accepted
    cases accepted

example (languages : Nat → Lang Symbol) (ranks : Nat → Nat → Lang Symbol)
    (finite : ∀ name term, languages name term ↔ ∃ rank, ranks name rank term)
    (term : Term Symbol) :
    ¬ IntersectSchedule.inputLanguage languages .empty term := by
  intro accepted
  obtain ⟨rank, accepted⟩ := input_finite languages ranks finite .empty term accepted
  cases accepted
end
end MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts.Probes
