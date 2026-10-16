import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterActual

namespace FiniteOrdinaryOuterRootKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialGraph (NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Actual source construction and completed root reads compose at one exact returned state. -/
theorem constructed_actual_root
    (width : Nat) {initial final : Cache.State Key} {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      DNode value ∧
      ∀ budget result after (actual : NodeCall budget ⟨emptyValue final, value⟩ (caller width final heap) result after)
        finalMemos, NodeCallReads formulas solver actual globals finalMemos → Checks (nodeCallTrace actual) →
        ∃ next, Post formulas solver next (caller width final heap) after finalMemos ∧
          Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧
          ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨value, heap, built, context, stored, resultDomain, identity, same, ready, available, _free, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed width history valid expression domain covered formulas solver
  refine ⟨value, heap, built, resultDomain, ?_⟩
  intro budget result after actual finalMemos reads checks
  have inherited : SourceEqualityConstraintAllocation.Ready
      (caller width final heap).checked.operations.constraints (emptyValue final) := by rw [same]; exact ready
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver
    reads (inventory expression value heap built) checks context inherited available
  obtain ⟨retained, narrowed⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_call formulas solver
    reads (inventory expression value heap built) checks context inherited available resultDomain stored
  refine ⟨next, post, output, retained, narrowed, ?_⟩
  intro ambient term
  apply (law ambient term).2
  simp [same, SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Domain construction covers nested ordered siblings with unrestricted complete guards. -/
theorem nested_guarded_source
    {S G : Type} [DecidableEq (EdgeKey S G)] (symbol : S) (constraint : G) :
    let leaf : InternedNestedConstruction.Syntax S G := .node [.mk symbol constraint []]
    let expression : InternedNestedConstruction.Syntax S G :=
      .node [.mk symbol constraint [leaf, leaf], .mk symbol constraint []]
    ∃ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧ InternedNestedFacts.Facts heap ∧ Available heap value := by
  apply SourceCurrentAllocatedFiniteOrdinaryConstruction.closed
  exact .ordinary (.cons (.cons (.ordinary (.cons .nil .nil))
    (.cons (.ordinary (.cons .nil .nil)) .nil)) (.cons .nil .nil))

end FiniteOrdinaryOuterRootKernels
#print axioms FiniteOrdinaryOuterRootKernels.constructed_actual_root
#check @FiniteOrdinaryOuterRootKernels.constructed_actual_root
#print axioms FiniteOrdinaryOuterRootKernels.nested_guarded_source
#check @FiniteOrdinaryOuterRootKernels.nested_guarded_source
