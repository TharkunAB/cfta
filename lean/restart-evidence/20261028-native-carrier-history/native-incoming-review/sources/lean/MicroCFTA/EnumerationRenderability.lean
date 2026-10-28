import MicroCFTA.EnumerationGraphReferences

/-!
# Renderability of completed enumeration states

The initialized caller preserves graph provenance for root zero, stored
fragment holes, and residual holes. Completion excludes their pending cases.
-/

namespace MicroCFTA.EnumerationRenderability
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction EnumerationOutConstruction EnumerationDecrease EnumerationHistogram EnumerationTermination EnumerationCarriers EnumerationGraphReferences

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Class-preserving reads retain all graph carriers. -/
theorem carriers_read (before after : State Symbol Guard) (stable : RenderStable before after) : PreservesCarriers before after :=
  carriers_classes before after stable.values (fun left right same => (stable.classes left right).mpr same)

/-- Class-preserving reads retain the graph provenance of every stored reference. -/
theorem references_read (before after : State Symbol Guard) (stable : RenderStable before after) (carried : ReferencesCarry before) : ReferencesCarry after :=
  references_transport before after carried (carriers_read before after stable)
    (fun uv fragment stored => by simpa [stable.values] using stored) stable.obligations

/-- Writing a completed fragment preserves carriers and retains its graph-bearing holes. -/
theorem write_references (before : State Symbol Guard) (uv : Nat) (fragment : Fragment Symbol)
    (carried : ReferencesCarry before) (holes : FragmentCarries before fragment) :
    PreservesCarriers before {before with values := before.values.set uv (.enumerated fragment)} ∧
      ReferencesCarry {before with values := before.values.set uv (.enumerated fragment)} := by
  have preserved := set_graph_carriers before uv (.enumerated fragment) trivial
  refine ⟨preserved, ?_, ?_⟩
  · intro held storedFragment stored
    by_cases same : held = uv
    · subst held
      by_cases inside : uv < before.values.length
      · have equal : storedFragment = fragment := by simpa [inside] using stored.symm
        subst storedFragment
        exact holes.preserve fragment preserved
      · simp [inside] at stored
    · have old : before.values[held]? = some (.enumerated storedFragment) := by simpa [Ne.symm same] using stored
      exact (carried.1 held storedFragment old).preserve storedFragment preserved
  · intro obligation member
    exact (carried.2 obligation member).preserve obligation.2 preserved

/-- The final selected-root write preserves all graph carriers and all stored reference provenance. -/
theorem enumerateOut_carriers (graph : Graph Symbol Guard) (fuel uv : Nat) (before after : State Symbol Guard)
    (fragment : Fragment Symbol) (ready : Ready uv before) (carried : ReferencesCarry before)
    (success : Success (enumerateOut graph fuel uv) before fragment after) :
    PreservesCarriers before after ∧ ReferencesCarry after := by
  unfold enumerateOut at success
  obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  have readStable := (getValue_storage (fuel + 1) uv before readState value ready.safe ready.inside reading).1
  have readCarriers := carriers_read before readState readStable
  have readReferences := references_read before readState readStable carried
  obtain ⟨readReady, _⟩ := getValue_ready (fuel + 1) uv before readState value ready reading
  cases value with
  | eliminated | enumerated _ => exact (reject_unsuccessful readState after fragment continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful readState after fragment continued).elim
      | some node =>
          obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have resolvedStable := representative_read (fuel + 1) uv root readState resolved readReady.safe readReady.inside resolution
          have resolvedCarriers := carriers_read readState resolved resolvedStable
          have resolvedReferences := references_read readState resolved resolvedStable readReferences
          obtain ⟨found, _, rootSame, resolvedSame⟩ := (representative_success (fuel + 1) uv readState resolved root).mp resolution
          obtain ⟨current, currentState, currentRead, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨currentSame, currentStateSame⟩ := (get_success resolved currentState current).mp currentRead
          subst current
          subst currentState
          obtain ⟨ignored, started, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ resolved started).mp bookkeeping
          obtain ⟨produced, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have bounds : ∀ sc ∈ scs, sc.var < resolved.counter := by
            have original := (getValue_storage (fuel + 1) uv before readState (.unenumerated (some node) scs) ready.safe ready.inside reading).2
            simpa [SlotBound, resolvedStable.counter] using original
          let ancestry := match graph.node node with
            | .recursive _ => (recursionKey node scs :: resolved.recursionAncestry root).eraseDups
            | _ => resolved.recursionAncestry root
          have startedReferences : ReferencesCarry {resolved with expansionAncestry := ancestry} := resolvedReferences
          have expanded := (enumeration_carriers graph fuel).1 _ _ {resolved with expansionAncestry := ancestry} expanded produced
            (ancestry_safe resolved ancestry resolvedStable.safe) bounds startedReferences expansion
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ _ cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ _ written).mp writing
          obtain ⟨_, afterSame⟩ := (success_pure produced fragment _ after).mp final
          subst after
          have written := write_references _ root produced expanded.2.1 expanded.2.2
          exact ⟨readCarriers.trans (resolvedCarriers.trans (expanded.1.trans written.1)), written.2⟩

/-- The actual scheduler scan leaves every retained obligation unchanged. -/
theorem findExpandable_obligations (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard) (available : Option (List Nat))
    (success : Success (findExpandable graph fuel) before available after) : after.obligations = before.obligations := by
  unfold findExpandable at success
  change Success (get >>= fun state => state.values.zipIdx.foldlM (collect graph fuel) ([], []) >>= finishScan) before available after at success
  obtain ⟨current, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨currentSame, readSame⟩ := (get_success before readState current).mp reading
  subst current
  subst readState
  obtain ⟨summary, scanned, traversal, final⟩ := (success_bind _ _ _ _ _).mp continued
  have same := foldlM_invariant (collect graph fuel) (fun state : State Symbol Guard => state.obligations = before.obligations) before.values.zipIdx
    (by
      intro entry member accumulator previous result next valid execution
      obtain ⟨candidates, blocked⟩ := accumulator
      obtain ⟨value, index⟩ := entry
      cases value with
      | eliminated | enumerated _ =>
          obtain ⟨_, same⟩ := (success_pure _ result previous next).mp execution
          simpa [same] using valid
      | unenumerated node scs =>
          unfold collect at execution
          obtain ⟨resolved, middle, scanning, final⟩ := (success_bind _ _ _ _ _).mp execution
          have same := foldlM_invariant (resolve fuel) (fun state : State Symbol Guard => state.obligations = before.obligations) scs
            (by
              intro sc member accumulator previous result next valid execution
              unfold resolve at execution
              obtain ⟨root, middle, resolution, final⟩ := (success_bind _ _ _ _ _).mp execution
              obtain ⟨_, same⟩ := (success_pure _ result middle next).mp final
              exact same ▸ (representative_obligations fuel sc.var root previous middle resolution).trans valid)
            blocked resolved previous middle valid scanning
          obtain ⟨_, exactState⟩ := (success_pure _ result middle next).mp final
          simpa [exactState] using same)
    ([], []) summary before scanned rfl traversal
  obtain ⟨_, afterSame⟩ := (finishScan_success summary scanned after available).mp final
  simpa [afterSame] using same

/-- A successful scheduler scan changes only the representative compression state. -/
theorem findExpandable_read (graph : Graph Symbol Guard) (fuel : Nat) (before after : State Symbol Guard) (available : Option (List Nat))
    (safe : Safe before) (success : Success (findExpandable graph fuel) before available after) : RenderStable before after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives safe.1.total
  have scanned := (findExpandable_exact graph fuel roots before after available paths success).1
  obtain ⟨afterSafe, counter⟩ := findExpandable_safety graph fuel before after available safe success
  exact ⟨afterSafe, counter, scanned.values, findExpandable_obligations graph fuel before after available success,
    fun left right => (class_iff after.representatives roots scanned.roots left right).trans (class_iff before.representatives roots paths left right).symm⟩

/-- The complete-graph caller preserves every carrier and every stored graph-bearing reference. -/
theorem enumerateFully_carriers (graph : Graph Symbol Guard) (complete : CompleteGraph graph)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle)
    (fuel : Nat) (oracleState : OracleState) (before after : State Symbol Guard) (safe : Safe before) (carried : ReferencesCarry before)
    (success : Success (enumerateFully graph order oracle fuel oracleState) before () after) :
    PreservesCarriers before after ∧ ReferencesCarry after := by
  induction fuel generalizing before oracleState with
  | zero => exact (success_failure .fuelExhausted before after () success).elim
  | succ fuel ih =>
      rw [fully_action] at success
      obtain ⟨available, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp success
      have scannedStable := findExpandable_read graph (fuel + 1) before scanned available safe scan
      have scannedCarriers := carriers_read before scanned scannedStable
      have scannedReferences := references_read before scanned scannedStable carried
      cases selected : pickNext (order oracleState) available with
      | done =>
          simp only [selected] at continued
          obtain ⟨_, same⟩ := (success_pure () () scanned after).mp continued
          subst after
          exact ⟨scannedCarriers, scannedReferences⟩
      | stuck =>
          simp only [selected] at continued
          exact (reject_unsuccessful scanned after () continued).elim
      | expand uv =>
          have ready := findExpandable_ready graph (fuel + 1) uv before scanned available (order oracleState) safe scan selected
          simp only [selected] at continued
          obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have readStable := (getValue_storage (fuel + 1) uv scanned readState value ready.safe ready.inside reading).1
          have readCarriers := carriers_read scanned readState readStable
          have readReferences := references_read scanned readState readStable scannedReferences
          have readReady := (getValue_ready (fuel + 1) uv scanned readState value ready reading).1
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
                  obtain ⟨_, acceptedSame⟩ := (require_success _ readState accepted).mp acceptance
                  subst accepted
                  obtain ⟨fragment, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  obtain ⟨expandedCarriers, expandedReferences⟩ := enumerateOut_carriers graph (fuel + 1) uv readState expanded fragment readReady readReferences expansion
                  have expandedSafe := (enumerateOut_safe graph (fuel + 1) uv readState expanded fragment readReady.safe readReady.inside readReady.root readReady.avoids expansion).1
                  obtain ⟨⟨afterReject, afterState⟩, observed, observation, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  have observedSame := observer beforeState uv (.inl fragment) expanded _ observed observation
                  subst observed
                  obtain ⟨ignored, accepted, acceptance, continued⟩ := (success_bind _ _ _ _ _).mp continued
                  cases ignored
                  obtain ⟨_, acceptedSame⟩ := (require_success _ expanded accepted).mp acceptance
                  subst accepted
                  obtain ⟨lastCarriers, lastReferences⟩ := ih afterState expanded expandedSafe expandedReferences continued
                  exact ⟨scannedCarriers.trans (readCarriers.trans (expandedCarriers.trans lastCarriers)), lastReferences⟩

/-- Initialization has no fragment holes or residual references. -/
theorem initial_references (root : Nat) : ReferencesCarry (initial root : State Symbol Guard) := by
  constructor
  · intro uv fragment stored
    cases uv <;> simp [initial] at stored
  · simp [initial]

/-- The initialized root and every completed stored reference keep their graph provenance. -/
theorem initialized_carriers (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (fuel root : Nat) (after : State Symbol Guard)
    (success : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after) :
    CarriesGraph after 0 ∧ ReferencesCarry after := by
  obtain ⟨preserved, references⟩ := enumerateFully_carriers graph complete (fun _ _ => none) noPruning noPruning_readOnly fuel () (initial root) after
    ⟨initial_storage root, initial_live root⟩ (initial_references root) success
  exact ⟨preserved 0 (carries_self (initial root) (initial_storage root).total 0 (.unenumerated (some root) []) rfl trivial), references⟩

/-- A graph carrier in safe storage is an allocated variable. -/
theorem carrier_inside (state : State Symbol Guard) (safe : Safe state) (uv : Nat) (carried : CarriesGraph state uv) : uv < state.counter := by
  obtain ⟨held, value, related, stored, _⟩ := carried
  have inside : held < state.counter := by rw [safe.1.aligned]; exact (List.getElem?_eq_some_iff.mp stored).1
  by_cases allocated : uv < state.counter
  · exact allocated
  · have same := outside_class state.representatives state.counter uv held safe.1.forest (by omega) related
    omega

/-- A completed complete-graph state stores an enumerated fragment at each graph carrier's representative. -/
theorem completed_carrier (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (state : State Symbol Guard)
    (safe : Safe state) (finished : Finished graph state) (uv root size : Nat) (carried : CarriesGraph state uv)
    (path : UnionFind.Reaches state.representatives uv root size) :
    ∃ fragment, state.values[root]? = some (.enumerated fragment) := by
  obtain ⟨held, value, related, stored, bearing⟩ := carried
  have live : value ≠ .eliminated := by cases value <;> simp_all [GraphValue]
  obtain ⟨heldSize, heldPath⟩ := (safe.2 held value stored).mp live
  have same : root = held := (UnionFind.sameClass_iff_roots path heldPath).mp related
  subst root
  cases value with
  | eliminated => cases bearing
  | enumerated fragment => exact ⟨fragment, stored⟩
  | unenumerated node scs =>
      cases node with
      | none => cases bearing
      | some node =>
          have done := finished _ (List.mem_of_getElem? stored)
          cases view : graph.node node with
          | recursive body => exact (complete.1 node body view).elim
          | empty | alternatives _ | unresolved _ => simp [candidate, view] at done

end MicroCFTA.EnumerationRenderability
