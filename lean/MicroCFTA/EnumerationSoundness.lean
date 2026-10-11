import MicroCFTA.EnumerationValidity

/-!
# Whole-caller assignment preservation

The complete graph caller derives its storage and trie invariants from the
input state. A successful final assignment implies the original restrictions.
-/

namespace MicroCFTA.EnumerationSoundness
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- The actual scheduler scan preserves all complete-assignment restrictions. -/
theorem findExpandable_assignment (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) (fuel : Nat)
    (before after : State Symbol Guard) (result : Option (List Nat)) (total : UnionFind.Total before.representatives)
    (success : Success (findExpandable graph fuel) before result after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before := by
  unfold findExpandable at success
  change Success (get >>= fun state => do
    let summary ← state.values.zipIdx.foldlM (collect graph fuel) ([], [])
    finishScan summary) before result after at success
  obtain ⟨current, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨currentSame, readSame⟩ := (get_success before readState current).mp reading
  subst current
  subst readState
  obtain ⟨summary, scanned, scanning, final⟩ := (success_bind _ _ _ _ _).mp continued
  let invariant := fun state : State Symbol Guard => UnionFind.Total state.representatives ∧
    (Satisfies language meaning assignment state ↔ Satisfies language meaning assignment before)
  have step : ∀ entry ∈ before.values.zipIdx, ∀ accumulator previous result next, invariant previous →
      Success (collect graph fuel accumulator entry) previous result next → invariant next := by
    intro entry _ accumulator previous result next valid success
    obtain ⟨value, index⟩ := entry
    obtain ⟨candidates, blocked⟩ := accumulator
    cases value with
    | eliminated | enumerated _ =>
        obtain ⟨_, same⟩ := (success_pure (candidates, blocked) result previous next).mp success
        subst next
        exact valid
    | unenumerated node scs =>
        unfold collect at success
        obtain ⟨blockedResult, resolved, traversal, final⟩ := (success_bind _ _ _ _ _).mp success
        have localStep : ∀ sc ∈ scs, ∀ accumulator old output new, invariant old →
            Success (resolve fuel accumulator sc) old output new → invariant new := by
          intro sc _ accumulator old output new oldValid resolution
          unfold resolve at resolution
          obtain ⟨root, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp resolution
          obtain ⟨middleTotal, equivalent⟩ := representative_assignment language meaning assignment fuel sc.var root old middle oldValid.1 reading
          obtain ⟨_, same⟩ := (success_pure (root :: accumulator) output middle new).mp final
          subst new
          exact ⟨middleTotal, equivalent.trans oldValid.2⟩
        have resolvedValid := foldlM_invariant (resolve fuel) invariant scs localStep blocked blockedResult previous resolved valid traversal
        obtain ⟨_, same⟩ := (success_pure _ result resolved next).mp final
        subst next
        exact resolvedValid
  have scannedValid := foldlM_invariant (collect graph fuel) invariant before.values.zipIdx step
    ([], []) summary before scanned ⟨total, Iff.rfl⟩ scanning
  obtain ⟨_, same⟩ := (finishScan_success summary scanned after result).mp final
  subst after
  exact scannedValid.2

/-- Scheduler scanning preserves the canonical stored tries. -/
theorem findExpandable_canonical (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) (total : UnionFind.Total before.representatives) (valid : Canonical before)
    (success : Success (findExpandable graph fuel) before result after) : Canonical after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  have values := (findExpandable_exact graph fuel roots before after result paths success).1.values
  intro value member
  exact valid value (by simpa [values] using member)

/-- A graph without recursive marker views never enters the recursion cutoff branch. -/
theorem checkRepeated_complete (graph : Graph Symbol Guard) (complete : CompleteGraph graph)
    (fuel uv node : Nat) (scs : List Suspended) (before after : State Symbol Guard) (repeated : Bool)
    (success : Success (checkRepeated graph fuel uv node scs) before repeated after) : repeated = false ∧ after = before := by
  cases view : graph.node node with
  | recursive body => exact (complete.1 node body view).elim
  | empty | alternatives _ | unresolved _ =>
      apply (success_pure false repeated before after).mp
      simpa [checkRepeated, view] using success

/-- The full actual complete-graph caller cannot discard an original restriction on successful assignments. -/
theorem enumerateFully_backward (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle) (fuel : Nat)
    (oracleState : OracleState) (before after : State Symbol Guard) (safe : Safe before) (valid : Canonical before)
    (success : Success (enumerateFully graph order oracle fuel oracleState) before () after)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after) :
    Satisfies (Accepted graph meaning) meaning assignment before := by
  induction fuel generalizing oracleState before with
  | zero => exact (success_failure .fuelExhausted before after () success).elim
  | succ fuel ih =>
      rw [fully_action] at success
      obtain ⟨available, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨scannedSafe, _⟩ := findExpandable_safety graph (fuel + 1) before scanned available safe scanning
      have scannedValid := findExpandable_canonical graph (fuel + 1) before scanned available safe.1.total valid scanning
      have scanExact := findExpandable_assignment graph (Accepted graph meaning) meaning assignment (fuel + 1)
        before scanned available safe.1.total scanning
      apply scanExact.mp
      cases selected : pickNext (order oracleState) available with
      | done =>
          simp only [selected] at continued
          obtain ⟨_, same⟩ := (success_pure () () scanned after).mp continued
          subst after
          exact satisfies
      | stuck =>
          simp only [selected] at continued
          exact (reject_unsuccessful scanned after () continued).elim
      | expand uv =>
          have ready := findExpandable_ready graph (fuel + 1) uv before scanned available (order oracleState) safe scanning selected
          simp only [selected] at continued
          obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨readReady, _⟩ := getValue_ready (fuel + 1) uv scanned readState value ready reading
          obtain ⟨readValid, _⟩ := getValue_canonical (fuel + 1) uv scanned readState value scannedValid reading
          apply (getValue_assignment (Accepted graph meaning) meaning assignment (fuel + 1) uv scanned readState value scannedSafe.1.total reading).mp
          cases value with
          | eliminated | enumerated _ => exact (reject_unsuccessful readState after () continued).elim
          | unenumerated node scs =>
              cases node with
              | none => exact (reject_unsuccessful readState after () continued).elim
              | some node =>
                  obtain ⟨repeated, checked, checking, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  obtain ⟨repeatedSame, checkedSame⟩ := checkRepeated_complete graph complete (fuel + 1) uv node scs readState checked repeated checking
                  subst repeated
                  subst checked
                  obtain ⟨⟨beforeReject, beforeState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have observedSame := observer oracleState uv (.inr node) readState _ observed observation
                  subst observed
                  obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  cases ignored
                  obtain ⟨_, same⟩ := (require_success (!beforeReject) readState accepted).mp acceptance
                  subst accepted
                  obtain ⟨fragment, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have expandedSafe := (enumerateOut_safe graph (fuel + 1) uv readState expanded fragment
                    readReady.safe readReady.inside readReady.root readReady.avoids expansion).1
                  have expandedValid := enumerateOut_canonical graph complete.2 (fuel + 1) uv readState expanded fragment readValid expansion
                  obtain ⟨⟨afterReject, afterState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have observedSame := observer beforeState uv (.inl fragment) expanded _ observed observation
                  subst observed
                  obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  cases ignored
                  obtain ⟨_, same⟩ := (require_success (!afterReject) expanded accepted).mp acceptance
                  subst accepted
                  have expandedSatisfies := ih afterState expanded expandedSafe expandedValid continued
                  exact (enumerateOut_backward graph meaning complete correct assignment (fuel + 1) uv readState expanded fragment readReady
                    (fun node scs stored => readValid _ (List.mem_of_getElem? stored)) expansion expandedSatisfies).1

/-- Every successful initialized complete caller retains the requested root language. -/
theorem initialized_assignment_accepted (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (fuel root : Nat) (after : State Symbol Guard)
    (success : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after) : Accepted graph meaning root (assignment 0) := by
  apply (initial_semantics (Accepted graph meaning) meaning assignment root).mp
  exact enumerateFully_backward graph meaning complete correct assignment (fun _ _ => none) noPruning noPruning_readOnly fuel ()
    (initial root) after ⟨initial_storage root, initial_live root⟩ (initial_canonical root) success satisfies

/-- Rendering preserves complete assignments because it changes only representative paths. -/
theorem renderStable_assignment (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before after : State Symbol Guard) (stable : RenderStable before after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before := by
  simp only [Satisfies, Fragments.stateSatisfies, stable.values, stable.obligations, UnionFind.Satisfies, stable.classes]

/-- A complete graph has no recursive marker branch in any rendering state. -/
theorem complete_noMarkers (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (state : State Symbol Guard) :
    NoMarkers graph state := by
  intro uv node scs stored body
  exact complete.1 node body

/-- Every output in a pointwise proof satisfies its output-only property. -/
theorem all₂_outputs (property : β → Prop) (left : List α) (right : List β)
    (related : All₂ (fun _ output => property output) left right) : ∀ output ∈ right, property output := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      intro output member
      rcases List.mem_cons.mp member with rfl | remaining
      · exact head
      · exact ih output remaining

/-- The actual initialized run returns an accepted term and true residuals under every satisfying final assignment. -/
theorem runs_assignment_sound (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (marker : Symbol) (fuel root : Nat)
    (term : Term Symbol) (pending : List (Guard × Term Symbol)) (after : State Symbol Guard)
    (success : .ok ((term, pending), after) ∈ runs graph marker fuel root)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after) :
    Accepted graph meaning root term ∧ ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  unfold runs at success
  change Success _ (initial root) (term, pending) after at success
  obtain ⟨ignored, enumerated, enumeration, continued⟩ := (success_bind _ _ _ _ _).mp success
  cases ignored
  obtain ⟨enumeratedSafe, supply⟩ := initialized_enumeration_safe graph fuel root enumerated enumeration
  obtain ⟨rendered, renderedState, rendering, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have rootBound : 0 < enumerated.counter := by omega
  have renderedStable := expandUVar_storage graph marker fuel 0 enumerated renderedState rendered enumeratedSafe rootBound rendering
  obtain ⟨current, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨currentSame, readSame⟩ := (get_success renderedState readState current).mp reading
  subst current
  subst readState
  obtain ⟨obligations, guarded, traversal, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨pairSame, afterSame⟩ := (success_pure (rendered, obligations) (term, pending) guarded after).mp final
  have termSame : term = rendered := congrArg Prod.fst pairSame
  have pendingSame : pending = obligations := congrArg Prod.snd pairSame
  subst term
  subst pending
  subst after
  let action := fun obligation : Guard × Fragment Symbol => do
    pure (obligation.1, ← expandFragment graph marker fuel obligation.2)
  have step : ∀ obligation ∈ renderedState.obligations, ∀ previous output next, RenderStable renderedState previous →
      Success (action obligation) previous output next → RenderStable renderedState next ∧
        (Satisfies (Accepted graph meaning) meaning assignment next →
          Satisfies (Accepted graph meaning) meaning assignment previous ∧ meaning output.1 output.2) := by
    intro obligation member previous output next valid renderSuccess
    obtain ⟨guardedTerm, middle, rendering, final⟩ := (success_bind _ _ _ _ _).mp renderSuccess
    have bounded : FragmentBound previous.counter obligation.2 := by
      rw [valid.counter]
      exact renderedStable.safe.1.guards obligation member
    have stable := expandFragment_storage graph marker fuel obligation.2 previous middle guardedTerm valid.safe bounded rendering
    obtain ⟨outputSame, stateSame⟩ := (success_pure (obligation.1, guardedTerm) output middle next).mp final
    subst output
    subst next
    refine ⟨valid.trans stable, ?_⟩
    intro afterHolds
    have beforeHolds := (renderStable_assignment (Accepted graph meaning) meaning assignment previous middle stable).mp afterHolds
    have exactTerm := (expandFragment_sound graph (Accepted graph meaning) meaning assignment marker fuel obligation.2 previous middle guardedTerm
      ⟨valid.safe.1.total, beforeHolds, complete_noMarkers graph complete previous⟩ rendering).2
    refine ⟨beforeHolds, ?_⟩
    rw [exactTerm]
    apply beforeHolds.2 obligation
    simpa [valid.obligations] using member
  obtain ⟨renderedSatisfies, residuals⟩ := mapM_backward action (RenderStable renderedState)
    (Satisfies (Accepted graph meaning) meaning assignment) (fun _ output => meaning output.1 output.2)
    renderedState.obligations step renderedState guarded obligations (.refl renderedState renderedStable.safe) traversal satisfies
  have enumeratedSatisfies := (renderStable_assignment (Accepted graph meaning) meaning assignment enumerated renderedState renderedStable).mp renderedSatisfies
  have rootAccepted := initialized_assignment_accepted graph meaning complete correct assignment fuel root enumerated enumeration enumeratedSatisfies
  have rootTerm := (expandUVar_sound graph (Accepted graph meaning) meaning assignment marker fuel 0 enumerated renderedState rendered
    ⟨enumeratedSafe.1.total, enumeratedSatisfies, complete_noMarkers graph complete enumerated⟩ rendering).2
  exact ⟨by simpa [rootTerm] using rootAccepted, all₂_outputs (fun obligation => meaning obligation.1 obligation.2) _ obligations residuals⟩

end MicroCFTA.EnumerationSoundness
