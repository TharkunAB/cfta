import MicroCFTA.SourceFreshOrdinaryColdBudgetReachability
import MicroCFTA.SourceFreshOrdinaryColdBudgetHeap
import MicroCFTA.InternedGuardedBudgetStoredRefinement

/-!
# Budget completeness of the actual final repaired graph

Actual Mu unfolding decreases the accepted budget. Union alternatives
decrease the stored value size. Constructor children decrease the term
size. These three measures give finite accepting graph runs. Replayed
rows supply availability and closedness at every epsilon step.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdBudgetCompleteness
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows Supported)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)
open SourceFreshOrdinaryColdBudgetReachability (Reached inputs next child)
open MergedFreshOrdinaryGraph
open InternedGuardedBudget
open BinderBudgetLanguage (Upward)

/-- Every accepted finite budget gives a finite actual graph run from each reached final-row value. -/
theorem reached_complete [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : InternedGuardedBudgetProbeHeap.Heap state)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows) (resident : ResidentRows state rows)
    (closedRows : CoveredRows rows rows) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (upward : ∀ name, Upward (ambient name)) (value : Value Symbol Guard) (reached : Reached state rows value)
    (budget : Nat) (term : Term Symbol) (accepted : meaning holds ambient value budget term) :
    EpsilonUnion.Accepts (graph state holds) value term := by
  have valid := inputs state semantic covered rows replayed value reached
  cases value with
  | empty => rw [meaning] at accepted; exact False.elim accepted
  | reference name => have impossible := valid.2; cases impossible
  | node entry edges depth free =>
      rw [meaning] at accepted
      obtain ⟨⟨edge, member⟩, accepted⟩ := accepted
      obtain ⟨terms, rfl, runs, guard⟩ := (edgeMeaning_all holds ambient budget edge term).mp accepted
      apply (node_exact state holds entry edges depth free _).mpr
      refine ⟨edge, member, terms, rfl, ?_, guard⟩
      apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ runs
      intro child childIn term termIn accepted
      exact reached_complete state semantic covered heap rows replayed resident closedRows holds ambient upward child
        (SourceFreshOrdinaryColdBudgetReachability.child state semantic covered rows replayed resident closedRows
          (.node entry edges depth free) reached edge member child childIn) budget term accepted
  | union entry members depth free =>
      rw [meaning] at accepted
      obtain ⟨⟨member, selected⟩, accepted⟩ := accepted
      have nextMember : member ∈ successors state (.union entry members depth free) := selected
      exact .reference nextMember (reached_complete state semantic covered heap rows replayed resident closedRows holds ambient
        upward member (next state rows _ reached member nextMember) budget term accepted)
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, _, _, _, _, _, _⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 valid.1 semantic.2 covered
      obtain ⟨smaller, less, accepted⟩ := InternedGuardedBudgetStoredRefinement.unfold_strict entry body depth ordinary state
        semantic.1 heap semantic.2 valid.1 result after done holds ambient upward budget term accepted
      have nextMember : result ∈ successors state (.mu entry body depth ordinary) := by simp only [successors, done, List.mem_singleton]
      exact .reference nextMember (reached_complete state semantic covered heap rows replayed resident closedRows holds ambient
        upward result (next state rows _ reached result nextMember) smaller term accepted)
termination_by (sizeOf term, budget, sizeOf value)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  · apply Prod.Lex.left
    have smaller := List.sizeOf_lt_of_mem termIn
    omega
  · apply Prod.Lex.right
    apply Prod.Lex.right
    have smaller := List.sizeOf_lt_of_mem selected
    omega
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ less)

/-- Every accepted budget of an available closed declared root belongs to the final graph. -/
theorem graph_complete [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : InternedGuardedBudgetProbeHeap.Heap state)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows) (resident : ResidentRows state rows)
    (closedRows : CoveredRows rows rows) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (upward : ∀ name, Upward (ambient name)) (value : Value Symbol Guard) (available : Available state value)
    (closed : value.free = []) (supported : Supported rows value) (budget : Nat) (term : Term Symbol)
    (accepted : meaning holds ambient value budget term) : EpsilonUnion.Accepts (graph state holds) value term :=
  reached_complete state semantic covered heap rows replayed resident closedRows holds ambient upward value
    (SourceFreshOrdinaryColdBudgetReachability.root state rows value available closed supported) budget term accepted

end MicroCFTA.SourceFreshOrdinaryColdBudgetCompleteness
