import MicroCFTA.InternedStoredPlanBinderDepthExact
import MicroCFTA.InternedFreshOrdinaryDepthHeap
import MicroCFTA.InternedFreshOrdinaryReadback

/-!
# Open-depth readback at canonical Mu requests

The existing cached-depth invariant determines the actual cleanup branch.
Equality of body and Depth-probe open depth then determines the exact
open-depth result. Preservation through complete source execution remains
a separate obligation.
-/
namespace MicroCFTA.InternedOpenDepthReadback
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (finish)
open InternedStoredPlanBinderDepth
open InternedBinderProtocol (NodeKey)

/-- One complete Mu has equal actual body and Depth-probe open depth. -/
def Correct (body depth : Value Symbol Guard) : Prop := valueDepth body = valueDepth depth

/-- Every complete Mu in the exact cache retains the body/probe open-depth equality. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) → Correct body depth

/-- Empty source caches contain no complete Mu obligation. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Effects that add no Mu preserve the body/probe equality. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before)
    (old : InternedShallowHeap.NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- Completing a request retains an earlier equality or installs its proved candidate. -/
theorem complete_heap (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) (correct : Correct body depth) :
    Heap (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- Actual cleanup has exact open depth from the stored Depth probe and its decoded local-use decision. -/
theorem finish_depth (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (cached : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary) (correct : Correct body depth) :
    valueDepth (finish smart (.mu entry body depth ordinary)) =
      if (finish smart (.mu entry body depth ordinary)).free.isEmpty then 0
      else if !smart || InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary then valueDepth depth + 1
      else valueDepth depth := by
  have bodyCached : body.depth = depth.depth := by
    have raw := (cached false).1
    simp only [finish, Bool.false_eq_true, ↓reduceIte, Value.depth,
      InternedFreshOrdinaryDepthHeap.decodedDepth, Bool.not_false, Bool.true_or] at raw
    omega
  by_cases closed : (finish smart (.mu entry body depth ordinary)).free.isEmpty = true
  · rw [ite_eq_left closed]
    exact closed_zero _ (List.isEmpty_iff.mp closed)
  · rw [ite_eq_right closed]
    cases smart with
    | false =>
        have opened : (Value.mu entry body depth ordinary).free.isEmpty ≠ true := by simpa [finish] using closed
        simp only [finish, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or]
        rw [valueDepth.eq_def, ite_eq_right opened]
        change 1 + valueDepth body = valueDepth depth + 1
        unfold Correct at correct
        omega
    | true =>
        have observed := (cached true).1
        by_cases unused : InternedBinderProtocol.Reference.interned entry.identity ∉ body.free
        · have finished : finish true (.mu entry body depth ordinary) = body := by simp [finish, cleanup, unused]
          rw [finished] at observed ⊢
          cases used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary with
          | false => simpa only [Correct, Bool.not_true, Bool.false_or, used, Bool.false_eq_true, ↓reduceIte] using correct
          | true =>
              simp only [InternedFreshOrdinaryDepthHeap.decodedDepth, used, Bool.not_true, Bool.false_or, ↓reduceIte] at observed
              omega
        · by_cases bare : body.referenceOf = .ref (.interned entry.identity)
          · have finished : finish true (.mu entry body depth ordinary) = .empty := by simp [finish, cleanup, unused, bare]
            simp only [finished, Value.free, List.isEmpty_nil, not_true_eq_false] at closed
          · have finished : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
              simp [finish, cleanup, unused, bare]
            rw [finished] at observed ⊢
            cases used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary with
            | false =>
                simp only [Value.depth, InternedFreshOrdinaryDepthHeap.decodedDepth, used,
                  Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at observed
                omega
            | true =>
                have opened : (Value.mu entry body depth ordinary).free.isEmpty ≠ true := by simpa only [finished] using closed
                simp only [Bool.not_true, Bool.false_or, ↓reduceIte]
                rw [valueDepth.eq_def, ite_eq_right opened]
                change 1 + valueDepth body = valueDepth depth + 1
                unfold Correct at correct
                omega

/-- A coherent canonical hit reads the exact requested probe and retains its open-depth equality. -/
theorem hit_depth (smart : Bool) (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (heap : Heap state)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    valueDepth (finish smart value) =
      if (finish smart value).free.isEmpty then 0
      else if !smart || InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary then valueDepth depth + 1
      else valueDepth depth := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  exact finish_depth smart entry body depth ordinary (cached _ entry body depth ordinary present)
    (heap _ entry body depth ordinary present)

/-- A completed actual source request has exact open-depth readback in its returned cache. -/
theorem request_depth [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedNestedConstruction.request smart depth ordinary
      (InternedFreshOrdinaryFacts.callback expression environment) state = .done value after)
    (heap : Heap after) (cached : InternedFreshOrdinaryDepthHeap.Heap after) :
    valueDepth value = if value.free.isEmpty then 0
      else if !smart || InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary then valueDepth depth + 1
      else valueDepth depth := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | none =>
      obtain ⟨body, afterBody, _, present, same⟩ :=
        InternedFreshOrdinaryReadback.request_miss_record smart expression environment depth ordinary
          state facts.coherent installed value after done
      rw [same]
      exact finish_depth smart _ body depth ordinary (cached _ _ body depth ordinary present)
        (heap _ _ body depth ordinary present)
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => simp only [InternedNestedConstruction.request, installed, present] at done; cases done
      | some stored =>
          simp only [InternedNestedConstruction.request, installed, present, InternedNestedConstruction.Outcome.done.injEq] at done
          cases done.1
          cases done.2
          exact hit_depth smart depth ordinary stored state facts depthAvailable ordinaryAvailable heap cached present

end MicroCFTA.InternedOpenDepthReadback
