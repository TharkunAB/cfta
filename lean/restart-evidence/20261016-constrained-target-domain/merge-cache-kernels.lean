import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCache

namespace MicroCFTA.FiniteOrdinaryMergeCacheReview
open Cache InternedConstructorTemplates InternedProbeProvenance SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Structural" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
variable {Symbol Guard : Type}

-- One completed candidate retains both physical and structural table invariants.
theorem completed_candidate [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (heap : State Symbol Guard) (memo : Memo Symbol Guard) (input candidate : Value Symbol Guard)
    (semantic : SemanticReady heap) (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (structural : Structural memo) (available : Available heap input) (candidateAvailable : Available heap candidate)
    (closed : input.free = [] → candidate.free = []) (domain : DNode input) (candidateDomain : DNode candidate) :
    SourceCurrentMemoMergeEffects.Stored heap (remember memo input candidate) ∧
      Structural (remember memo input candidate) ∧
      remember memo input candidate input.referenceOf = some (winner memo input candidate) ∧
      (winner memo input candidate).original = input ∧ DNode (winner memo input candidate).result ∧
      Extends memo (remember memo input candidate) := by
  have physicalAfter := SourceCurrentMemoMergeEffects.stored_remember physical input candidate available candidateAvailable closed
  have structuralAfter := SourceCurrentAllocatedFiniteOrdinaryMergeCache.remember_stored structural input candidate (fun _ => candidateDomain)
  have winner := SourceCurrentAllocatedFiniteOrdinaryMergeCache.winner_domain semantic available physical structural domain candidateDomain
  exact ⟨physicalAfter, structuralAfter, winner_found memo input candidate, winner.1, winner.2, remember_extends _ _ _⟩

-- An earlier winner skips the candidate law and keeps the complete stored owner.
theorem earlier_winner [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (heap : State Symbol Guard) (memo : Memo Symbol Guard) (input candidate : Value Symbol Guard)
    (entry : Entry Symbol Guard) (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (structural : Structural memo)
    (domain : DNode input) (found : memo input.referenceOf = some entry) :
    remember memo input candidate = memo ∧ winner memo input candidate = entry ∧
      entry.original = input ∧ DNode entry.result := by
  have selected := winner_existing memo input candidate entry found
  have readback := SourceCurrentAllocatedFiniteOrdinaryMergeCache.hit_domain semantic available physical structural domain found
  exact ⟨selected.1, selected.2, readback.1, readback.2⟩

-- Serial completions preserve the first returned entry even at a repeated physical key.
theorem serial_candidates (memo : Memo Symbol Guard) (first second one two : Value Symbol Guard)
    (stored : Structural memo) (firstLaw : DNode first → DNode one) (secondLaw : DNode second → DNode two) :
    Structural (remember (remember memo first one) second two) ∧
      Extends memo (remember (remember memo first one) second two) ∧
      remember (remember memo first one) second two first.referenceOf = some (winner memo first one) := by
  have middle := SourceCurrentAllocatedFiniteOrdinaryMergeCache.remember_stored stored first one firstLaw
  have final := SourceCurrentAllocatedFiniteOrdinaryMergeCache.remember_stored middle second two secondLaw
  exact ⟨final, extends_trans (remember_extends _ _ _) (remember_extends _ _ _),
    remember_extends _ _ _ _ _ (winner_found memo first one)⟩

-- Actual Empty miss then hit retains its winner even for a proposed reference candidate.
theorem empty_miss_then_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (heap : State Symbol Guard) (name : InternedBinderProtocol.Reference) :
    let memo : Memo Symbol Guard := remember empty .empty .empty
    Call clear top .empty heap empty .empty heap memo ∧
      Call clear top .empty heap memo .empty heap memo ∧ Structural memo ∧
      remember memo .empty (.reference name) = memo ∧
      winner memo .empty (.reference name) = ⟨.empty, .empty⟩ ∧
      DNode (winner memo .empty (.reference name)).result ∧ ¬ DNode (.reference name : Value Symbol Guard) := by
  dsimp only
  have inserted := remember_absent (empty : Memo Symbol Guard) .empty .empty rfl
  have first : Call clear top .empty heap empty (winner empty .empty .empty).result heap (remember empty .empty .empty) :=
    .miss rfl (.pure (.empty : Value Symbol Guard) heap empty)
  rw [inserted.2] at first
  have preserved := winner_existing (remember (empty : Memo Symbol Guard) .empty .empty) .empty (.reference name)
    ⟨.empty, .empty⟩ inserted.1
  refine ⟨first, .hit inserted.1,
    SourceCurrentAllocatedFiniteOrdinaryMergeCache.remember_stored SourceCurrentAllocatedFiniteOrdinaryMergeCache.empty_stored
      .empty .empty (fun _ => .empty), preserved.1, preserved.2, ?_, ?_⟩
  · rw [preserved.2]
    exact .empty
  · exact SourceCurrentAllocatedFiniteOrdinaryDomain.not_reference name
end MicroCFTA.FiniteOrdinaryMergeCacheReview
#print axioms MicroCFTA.FiniteOrdinaryMergeCacheReview.completed_candidate
#check @MicroCFTA.FiniteOrdinaryMergeCacheReview.completed_candidate
#print axioms MicroCFTA.FiniteOrdinaryMergeCacheReview.earlier_winner
#check @MicroCFTA.FiniteOrdinaryMergeCacheReview.earlier_winner
#print axioms MicroCFTA.FiniteOrdinaryMergeCacheReview.serial_candidates
#check @MicroCFTA.FiniteOrdinaryMergeCacheReview.serial_candidates
#print axioms MicroCFTA.FiniteOrdinaryMergeCacheReview.empty_miss_then_hit
#check @MicroCFTA.FiniteOrdinaryMergeCacheReview.empty_miss_then_hit
