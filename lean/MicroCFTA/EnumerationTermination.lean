import MicroCFTA.EnumerationHistogram

/-!
# Existence of a complete scheduled enumeration

The actual scheduler always finishes or selects work. A selected expansion
strictly decreases the finite height histogram of its satisfying assignment.
-/

namespace MicroCFTA.EnumerationTermination
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction EnumerationOutConstruction EnumerationDecrease EnumerationHistogram

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Successful execution is available at every bound above its first successful bound. -/
theorem atLeast (action : Nat → EnumerateM Symbol Guard α)
    (more : ∀ fuel extra, Retains (action fuel) (action (fuel + extra))) (fuel larger : Nat) (bound : fuel ≤ larger)
    (before after : State Symbol Guard) (value : α) (success : Success (action fuel) before value after) :
    Success (action larger) before value after := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  exact more fuel extra before value after success

/-- Array-preserving reads preserve the complete height histogram. -/
theorem histogram_values (before after : State Symbol Guard) (assignment : Nat → Term Symbol) (same : after.values = before.values) :
    histogram after assignment = histogram before assignment := by
  classical
  funext height
  simp only [histogram, workAt, GraphPending, same]
  rfl

/-- Array-preserving reads preserve the fixed height bound. -/
theorem boundedWork_values (before after : State Symbol Guard) (assignment : Nat → Term Symbol) (bound : Nat)
    (same : after.values = before.values) (bounded : BoundedWork bound before assignment) : BoundedWork bound after assignment := by
  intro uv pending
  apply bounded uv
  simpa [GraphPending, same] using pending

/-- Complete graph views always allow the actual nonrepeated bookkeeping action. -/
theorem checkRepeated_terminates (graph : Graph Symbol Guard) (complete : CompleteGraph graph)
    (fuel uv node : Nat) (scs : List Suspended) (before : State Symbol Guard) :
    Success (checkRepeated graph fuel uv node scs) before false before := by
  cases view : graph.node node with
  | recursive body => exact (complete.1 node body view).elim
  | empty | alternatives _ | unresolved _ =>
      simpa [checkRepeated, view] using (success_pure false false before before).mpr ⟨rfl, rfl⟩

/-- Every safe proper satisfying complete state has a successful sufficiently bounded full caller execution. -/
theorem enumerateFully_complete (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (bound : Nat) (before : State Symbol Guard) (assignment : Nat → Term Symbol)
    (safe : Safe before) (proper : ProperState before) (pending : PendingReferences before)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before) (bounded : BoundedWork bound before assignment) :
    ∃ fuel after extended, Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) before () after ∧
      Satisfies (Accepted graph meaning) meaning extended after ∧
      (∀ uv < before.counter, extended uv = assignment uv) := by
  have construct : ∀ counts, ∀ (before : State Symbol Guard) (assignment : Nat → Term Symbol), histogram before assignment = counts →
      Safe before → ProperState before → PendingReferences before → Satisfies (Accepted graph meaning) meaning assignment before →
      BoundedWork bound before assignment →
      ∃ fuel after extended, Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) before () after ∧
        Satisfies (Accepted graph meaning) meaning extended after ∧ (∀ uv < before.counter, extended uv = assignment uv) := by
    intro counts
    induction counts using (HeightOrder.below_wellFounded bound).induction with
    | h counts ih =>
        intro before assignment countsSame safe proper pending satisfies bounded
        obtain ⟨scanFuel, available, scanned, scan, notBlocked⟩ := findExpandable_progress graph meaning assignment before safe proper satisfies
        obtain ⟨scannedSafe, scannedCounter⟩ := findExpandable_safety graph scanFuel before scanned available safe scan
        obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
        have scannedValues := (findExpandable_exact graph scanFuel roots before scanned available paths scan).1.values
        have scannedSatisfies := (findExpandable_assignment graph (Accepted graph meaning) meaning assignment scanFuel before scanned available safe.1.total scan).mpr satisfies
        cases available with
        | none =>
            refine ⟨scanFuel + 1, scanned, assignment, ?_, scannedSatisfies, by simp⟩
            rw [fully_action]
            exact (success_bind _ _ _ _ _).mpr ⟨none, scanned, findExpandable_moreFuel graph scanFuel 1 before none scanned scan,
              (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        | some available =>
            cases available with
            | nil => exact (notBlocked rfl).elim
            | cons uv rest =>
                have selected : pickNext (fun _ => none) (some (uv :: rest)) = .expand uv := rfl
                have ready := findExpandable_ready graph scanFuel uv before scanned (some (uv :: rest)) (fun _ => none) safe scan selected
                obtain ⟨value, stored, candidateTrue⟩ := (findExpandable_safe graph scanFuel before scanned (uv :: rest) uv safe.1.total safe.2 scan (by simp)).2.2.1
                have pendingSlot : ∃ node scs, value = .unenumerated (some node) scs := by
                  cases value with
                  | eliminated | enumerated _ => cases candidateTrue
                  | unenumerated node scs =>
                      cases node with
                      | none => cases candidateTrue
                      | some node => exact ⟨node, scs, rfl⟩
                obtain ⟨node, scs, rfl⟩ := pendingSlot
                have scannedProper := findExpandable_proper graph scanFuel before scanned (some (uv :: rest)) safe.1.total proper scan
                have scannedPending := findExpandable_pending graph scanFuel before scanned (some (uv :: rest)) safe.1.total pending scan
                have scannedIncoming := selected_incoming graph scanFuel uv before scanned (some (uv :: rest)) (fun _ => none) safe scan selected
                obtain ⟨readFuel, readState, reading⟩ := getValue_terminates scanned scannedSafe uv ready.root _ stored
                obtain ⟨readReady, readCounter⟩ := getValue_ready readFuel uv scanned readState _ ready reading
                have readStable := (getValue_storage readFuel uv scanned readState _ scannedSafe ready.inside reading).1
                have readStored := (getValue_root readFuel uv scanned readState _ scannedSafe ready.inside ready.root reading).2.2.2
                have readProper := (getValue_proper readFuel uv scanned readState _ scannedProper reading).1
                have readPending := pending_read scanned readState readStable scannedPending
                have readIncoming := incoming_read uv scanned readState readStable scannedIncoming
                have readSatisfies := (getValue_assignment (Accepted graph meaning) meaning assignment readFuel uv scanned readState _ scannedSafe.1.total reading).mpr scannedSatisfies
                have readBounded := boundedWork_values before readState assignment bound (readStable.values.trans scannedValues) bounded
                have readGraphPending : GraphPending readState uv := ⟨node, scs, readStored⟩
                obtain ⟨outFuel, fragment, expanded, extended, expansion, expandedSatisfies, outAgree, _⟩ := enumerateOut_complete graph meaning complete correct
                  readState assignment uv node scs readReady (proper_canonical readState readProper) readPending readStored readSatisfies
                obtain ⟨expandedSafe, growth, _⟩ := enumerateOut_safe graph outFuel uv readState expanded fragment readReady.safe readReady.inside readReady.root readReady.avoids expansion
                have expandedProper := enumerateOut_proper graph complete.2 outFuel uv readState expanded fragment readProper expansion
                have expandedPending := enumerateOut_pending graph outFuel uv readState expanded fragment readReady readPending readIncoming expansion
                have expandedBounded := enumerateOut_bounded graph meaning complete correct assignment extended outFuel uv bound readState expanded fragment readReady readProper readGraphPending
                  outAgree readBounded expansion expandedSatisfies
                have decrease := enumerateOut_histogram graph meaning complete correct assignment extended outFuel uv bound readState expanded fragment readReady readProper readGraphPending
                  outAgree (readBounded uv readGraphPending) expansion expandedSatisfies
                have readCounts : histogram readState assignment = counts := (histogram_values before readState assignment (readStable.values.trans scannedValues)).trans countsSame
                obtain ⟨restFuel, after, finalAssignment, continued, afterSatisfies, restAgree⟩ := ih (histogram expanded extended) (readCounts ▸ decrease)
                  expanded extended rfl expandedSafe expandedProper expandedPending expandedSatisfies expandedBounded
                let fuel := scanFuel + readFuel + outFuel + restFuel
                have scanMore : Success (findExpandable graph (fuel + 1)) before (some (uv :: rest)) scanned :=
                  atLeast _ (findExpandable_moreFuel graph) scanFuel (fuel + 1) (by dsimp [fuel]; omega) before scanned _ scan
                have readMore : Success (getValue (fuel + 1) uv) scanned (.unenumerated (some node) scs) readState :=
                  atLeast _ (fun fuel extra => getValue_moreFuel fuel extra uv) readFuel (fuel + 1) (by dsimp [fuel]; omega) scanned readState _ reading
                have outMore : Success (enumerateOut graph (fuel + 1) uv) readState fragment expanded :=
                  atLeast _ (fun fuel extra => enumerateOut_moreFuel graph fuel extra uv) outFuel (fuel + 1) (by dsimp [fuel]; omega) readState expanded fragment expansion
                have restMore : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) expanded () after :=
                  atLeast _ (fun fuel extra => enumerateFully_moreFuel graph (fun _ _ => none) noPruning fuel extra ()) restFuel fuel (by dsimp [fuel]; omega) expanded after () continued
                refine ⟨fuel + 1, after, finalAssignment, ?_, afterSatisfies, ?_⟩
                · rw [fully_action]
                  apply (success_bind _ _ _ _ _).mpr
                  refine ⟨some (uv :: rest), scanned, scanMore, ?_⟩
                  change Success (getValue (fuel + 1) uv >>= _) scanned () after
                  apply (success_bind _ _ _ _ _).mpr
                  refine ⟨.unenumerated (some node) scs, readState, readMore, ?_⟩
                  apply (success_bind _ _ _ _ _).mpr
                  refine ⟨false, readState, checkRepeated_terminates graph complete (fuel + 1) uv node scs readState, ?_⟩
                  apply (success_bind _ _ _ _ _).mpr
                  refine ⟨(false, ()), readState, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
                  apply (success_bind _ _ _ _ _).mpr
                  refine ⟨(), readState, (require_success _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
                  apply (success_bind _ _ _ _ _).mpr
                  refine ⟨fragment, expanded, outMore, ?_⟩
                  apply (success_bind _ _ _ _ _).mpr
                  refine ⟨(false, ()), expanded, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
                  exact (success_bind _ _ _ _ _).mpr ⟨(), expanded, (require_success _ _ _).mpr ⟨rfl, rfl⟩, restMore⟩
                · intro index inside
                  have readInside : index < readState.counter := by simpa [readCounter, scannedCounter] using inside
                  exact (restAgree index (Nat.lt_of_lt_of_le readInside growth)).trans (outAgree index readInside)
  exact construct (histogram before assignment) before assignment rfl safe proper pending satisfies bounded

/-- Every accepted root term has a successful initialized full caller execution preserving its witness. -/
theorem initialized_complete (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (root : Nat) (term : Term Symbol) (accepted : Accepted graph meaning root term) :
    ∃ fuel after assignment, Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after ∧
      Satisfies (Accepted graph meaning) meaning assignment after ∧ assignment 0 = term := by
  let assignment : Nat → Term Symbol := fun _ => term
  have initialSatisfies := (initial_semantics (Accepted graph meaning) meaning assignment root).mpr accepted
  have bounded : BoundedWork (term.height + 1) (initial root : State Symbol Guard) assignment := fun _ _ => by simp [assignment]
  obtain ⟨fuel, after, extended, execution, satisfies, agree⟩ := enumerateFully_complete graph meaning complete correct (term.height + 1)
    (initial root) assignment ⟨initial_storage root, initial_live root⟩ (initial_proper root) (initial_pending root) initialSatisfies bounded
  exact ⟨fuel, after, extended, execution, satisfies, agree 0 (by simp [initial])⟩

end MicroCFTA.EnumerationTermination
