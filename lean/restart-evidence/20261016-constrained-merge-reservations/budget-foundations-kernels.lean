import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode

namespace MicroCFTA.MergeBudgetFoundationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady)
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryReservations (observe nodeRequests edgeRequests)
open MergedOrdinaryHeight (height)
namespace N
export SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
end N
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Zero height is free, and a two-level expansion uses the squared lower row limit. -/
theorem numeric_expansion :
    N.nodeBudget 2 3 0 = 0 ∧ N.edgeBudget 2 3 0 = 0 ∧
      N.nodeBudget 2 3 2 = 85 ∧ N.edgeBudget 2 3 2 = 26 ∧
      N.nodeBudget 7 0 2 = 1 ∧ N.edgeBudget 7 0 2 = 7 := by decide

/-- Three mixed requests retain their variable costs and exact positional outputs. -/
theorem mixed_map (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) :
    Certified clear (map (fun kind : Bool => if kind then
      .bind (.work (makeNode [])) (fun _ => .pure ()) else
      .bind (.work (makeEdge symbol guard [])) (fun _ => .pure ())) [false, true, false]) before
      (fun after outputs => Budget before after 1 2 ∧
        Language.All₂ (fun (_ : Bool) output => output = ()) [false, true, false] outputs ∧ outputs.length = 3) := by
  have checked := map_certified clear
    (fun kind : Bool => if kind then .bind (.work (makeNode [])) (fun _ => .pure ())
      else .bind (.work (makeEdge symbol guard [])) (fun _ => .pure ()))
    (fun _ (_ : Bool) => True) (fun _ (_ : Bool) output => output = ())
    (fun _ _ _ _ valid => valid) (fun _ _ _ _ _ valid => valid)
    (fun kind => if kind then 1 else 0) (fun kind => if kind then 0 else 1)
    [false, true, false] ?_ before semantic costs (fun _ _ => True.intro)
  · exact checked.mono (fun _ outputs returned =>
      ⟨by simpa using returned.1, returned.2, by simpa using returned.2.length_eq.symm⟩)
  · intro kind _ heap semantic costs _
    cases kind with
    | false =>
        apply bind_certified clear _ _ heap (fun after edge => Budget heap after 0 1 ∧ EdgeReady after edge) _
          (edge_certified clear symbol guard [] heap semantic costs (by intro value member; cases member)
            (by intro value member; cases member))
        intro edge after _ valid
        exact ⟨valid.1, rfl⟩
    | true =>
        apply bind_certified clear _ _ heap (fun after value => Budget heap after 1 0 ∧ ValueReady after value) _
          (node_certified clear [] heap semantic costs (by intro edge member; cases member)
            (by intro edge member; cases member))
        intro value after _ valid
        exact ⟨valid.1, rfl⟩

omit [DecidableEq Symbol] in
/-- A repeated edge request consumes two requests but at most one reservation. -/
theorem warm_edge_requests (symbol : Symbol) (guard : Guard) (before : State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent before) :
    let first := run (makeEdge symbol guard []) before
    let second := run (makeEdge symbol guard []) first.2
    second = first ∧ Budget before second.2 0 2 ∧
      second.2.edges.next ≤ before.edges.next + 1 ∧
      edgeRequests (observe (makeEdge symbol guard []) before ++ observe (makeEdge symbol guard []) first.2) = 2 := by
  dsimp only
  have same := replay (makeEdge symbol guard []) before (run (makeEdge symbol guard []) before).2 coherent.valid (grows_refl _)
  have budget := (edge_work symbol guard [] before).trans (edge_work symbol guard [] (run (makeEdge symbol guard []) before).2)
  have supply := SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_next symbol guard [] before
  refine ⟨same, by simpa only [Nat.zero_add] using budget, ?_, ?_⟩
  · rw [same]
    exact supply.2
  · rw [SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.edgeRequests_append]
    simp [SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe, edgeRequests]

/-- A recursive request certificate gives a budget for its own exact start and return. -/
theorem request_original_budget (clear : Guard → Bool) (input : Value Symbol Guard)
    (before : State Symbol Guard) (available : Available before input)
    (rows arity bound : Nat) (profile : NodeShape rows arity input) (bounded : height input ≤ bound) :
    Certified clear (.request input) before (fun after output =>
      Budget before after (N.nodeBudget rows arity bound) (N.edgeBudget rows arity bound) ∧
        SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode.Contract input before output after) := by
  exact (request_certified clear input before available).mono
    (fun _ _ returned => ⟨returned.2 rows arity bound profile bounded, returned.1⟩)

#print axioms numeric_expansion
#check @numeric_expansion
#print axioms mixed_map
#check @mixed_map
#print axioms warm_edge_requests
#check @warm_edge_requests
#print axioms request_original_budget
#check @request_original_budget
end MicroCFTA.MergeBudgetFoundationKernels
