import MicroCFTA.EnumerationCarriers

/-!
# Graph-bearing holes in stored fragments and residuals

The source creates a hole only after attaching a graph restriction.
Every later state transition preserves that class provenance.
-/

namespace MicroCFTA.EnumerationGraphReferences
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction EnumerationOutConstruction EnumerationDecrease EnumerationHistogram EnumerationTermination EnumerationCarriers

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- Each hole in a fragment has a class that carries a graph restriction or completed fragment. -/
def FragmentCarries (state : State Symbol Guard) (fragment : Fragment Symbol) : Prop :=
  ∀ uv, HasHole fragment uv → CarriesGraph state uv

/-- Stored fragments and retained residuals refer only to graph-bearing classes. -/
def ReferencesCarry (state : State Symbol Guard) : Prop :=
  (∀ (uv : Nat) (fragment : Fragment Symbol), state.values[uv]? = some (.enumerated fragment) → FragmentCarries state fragment) ∧
    ∀ obligation ∈ state.obligations, FragmentCarries state obligation.2

/-- Carrier preservation retains every hole of an earlier fragment. -/
theorem FragmentCarries.preserve (fragment : Fragment Symbol) (carried : FragmentCarries before fragment)
    (preserved : PreservesCarriers before after) : FragmentCarries after fragment := fun uv hole => preserved uv (carried uv hole)

/-- A symbol fragment carries its holes exactly when each child does. -/
theorem fragmentCarries_node (state : State Symbol Guard) (symbol : Symbol) (children : List (Fragment Symbol))
    (carried : ∀ child ∈ children, FragmentCarries state child) : FragmentCarries state (.node symbol children) := by
  intro uv hole
  cases hole with
  | child _ _ child _ member hole => exact carried child member uv hole

/-- A hole carries its class when the variable has a graph carrier. -/
theorem fragmentCarries_hole (state : State Symbol Guard) (uv : Nat) (carried : CarriesGraph state uv) : FragmentCarries state (.hole uv) := by
  intro other hole
  cases hole
  exact carried

/-- Old fragments and unchanged obligations retain graph-bearing references. -/
theorem references_transport (before after : State Symbol Guard) (carried : ReferencesCarry before)
    (preserved : PreservesCarriers before after) (origin : EnumeratedOrigin before after)
    (obligations : after.obligations = before.obligations) : ReferencesCarry after := by
  refine ⟨?_, ?_⟩
  · intro uv fragment stored
    exact (carried.1 uv fragment (origin uv fragment stored)).preserve fragment preserved
  · intro obligation member
    exact (carried.2 obligation (by simpa [obligations] using member)).preserve obligation.2 preserved

/-- Representative lookup changes no retained residual. -/
theorem representative_obligations (fuel uv root : Nat) (before after : State Symbol Guard)
    (success : Success (representative fuel uv) before root after) : after.obligations = before.obligations := by
  obtain ⟨found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  rfl

/-- Equality union changes no retained residual. -/
theorem union_obligations (fuel left right : Nat) (before after : State Symbol Guard)
    (success : Success (unionVariables fuel left right) before () after) : after.obligations = before.obligations := by
  obtain ⟨forest, _, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  rfl

/-- Assimilation changes no retained residual. -/
theorem assimilate_obligations (graph : Graph Symbol Guard) (target source : Nat) (before after : State Symbol Guard)
    (success : Success (EnumerationState.assimilate graph target source) before () after) : after.obligations = before.obligations := by
  by_cases same : target = source
  · subst source
    have stateSame : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    rw [stateSame]
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, sourceState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨_, sourceSame⟩ := (rawValue_success source before sourceState sourceValue).mp reading
    subst sourceState
    cases sourceValue with
    | eliminated => rw [((success_pure () () before after).mp continued).2]
    | enumerated fragment =>
        obtain ⟨targetValue, targetState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        exact (success_failure .invalidIntersection targetState after () continued).elim
    | unenumerated sourceNode sourceScs =>
        obtain ⟨targetValue, targetState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨_, targetSame⟩ := (rawValue_success target before targetState targetValue).mp reading
        subst targetState
        cases intersection : intersectValues graph (.unenumerated sourceNode sourceScs) targetValue with
        | none =>
            simp only [intersection] at continued
            exact (success_failure .invalidIntersection before after () continued).elim
        | some merged =>
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            obtain ⟨_, same⟩ := (require_success _ before checked).mp required
            subst checked
            obtain ⟨ignored, written, writing, continued⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            obtain rfl := (modify_success _ before written).mp writing
            obtain ⟨ignored, eliminated, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            obtain rfl := (modify_success _ _ eliminated).mp writing
            rw [(modify_success _ _ after).mp final]

/-- Node restriction changes no retained residual. -/
theorem mergeNode_obligations (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended) (before after : State Symbol Guard)
    (success : Success (mergeNode graph fuel uv node scs) before () after) : after.obligations = before.obligations := by
  unfold mergeNode at success
  obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp success
  have same := representative_obligations fuel uv root before resolved resolution
  obtain ⟨previous, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨_, readSame⟩ := (rawValue_success root resolved readState previous).mp reading
  subst readState
  cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
  | none =>
      simp only [intersection] at continued
      exact (success_failure .invalidIntersection resolved after () continued).elim
  | some merged =>
      simp only [intersection] at continued
      obtain ⟨ignored, written, writing, continued⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ resolved written).mp writing
      obtain ⟨ignored, inherited, inheritance, final⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain rfl := (modify_success _ _ inherited).mp inheritance
      obtain ⟨_, afterSame⟩ := (require_success _ _ after).mp final
      rw [afterSame]
      exact same

/-- The complete terminal merge changes no retained residual. -/
theorem mergeTerminal_obligations (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (root : Nat) (success : Success (mergeTerminal graph fuel first rest) before root after) :
    after.obligations = before.obligations := by
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedSame := mapM_invariant (fun sc => representative fuel sc.var)
    (fun state : State Symbol Guard => state.obligations = before.obligations) (first :: rest)
    (fun sc _ previous result next valid execution => (representative_obligations fuel sc.var result previous next execution).trans valid)
    before scanned recorded rfl scan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedSame := forM_invariant (fun sc => unionVariables fuel first.var sc.var)
    (fun state : State Symbol Guard => state.obligations = before.obligations) rest
    (fun sc _ previous next valid execution => (union_obligations fuel first.var sc.var previous next execution).trans valid)
    scanned united scannedSame unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedSame := (representative_obligations fuel first.var winner united resolved resolution).trans unitedSame
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have assimilatedSame := forM_invariant (EnumerationState.assimilate graph winner)
    (fun state : State Symbol Guard => state.obligations = before.obligations) recorded
    (fun source _ previous next valid execution => (assimilate_obligations graph winner source previous next execution).trans valid)
    resolved assimilated resolvedSame assimilation
  obtain ⟨_, afterSame⟩ := (success_pure winner root assimilated after).mp final
  rw [afterSame]
  exact assimilatedSame

/-- A fresh equality batch changes no retained residual. -/
theorem suspended_obligations (count : Nat) (before : State Symbol Guard) : (suspendedState count before).obligations = before.obligations := by
  induction count generalizing before with
  | zero => rfl
  | succ count ih => exact ih (allocated none before)

/-- Fresh equality allocation retains the graph provenance of every earlier reference. -/
theorem suspension_references (count : Nat) (before : State Symbol Guard) (carried : ReferencesCarry before) : ReferencesCarry (suspendedState count before) :=
  references_transport before _ carried (suspension_carriers count before) (suspension_origin count before) (suspended_obligations count before)

/-- Recording a guarded fragment retains old graph provenance and adds its own carried holes. -/
theorem recordResidual_references (residual : Option Guard) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (carried : ReferencesCarry before) (holes : FragmentCarries before fragment)
    (success : Success (recordResidual residual fragment) before () after) : ReferencesCarry after := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact carried
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      refine ⟨carried.1, ?_⟩
      intro obligation member
      rcases List.mem_cons.mp member with rfl | old
      · exact holes
      · exact carried.2 obligation old

/-- Ordered traversal preserves all old graph carriers and all returned fragment holes. -/
theorem mapM_carriers (action : α → EnumerateM Symbol Guard (Fragment Symbol)) (invariant : State Symbol Guard → Prop)
    (inputs : List α)
    (step : ∀ input ∈ inputs, ∀ before fragment after, invariant before → Success (action input) before fragment after →
      invariant after ∧ PreservesCarriers before after ∧ FragmentCarries after fragment)
    (before after : State Symbol Guard) (fragments : List (Fragment Symbol)) (valid : invariant before)
    (success : Success (inputs.mapM action) before fragments after) :
    invariant after ∧ PreservesCarriers before after ∧ ∀ fragment ∈ fragments, FragmentCarries after fragment := by
  induction inputs generalizing before fragments with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] fragments before after).mp success
      exact ⟨valid, .refl _, by simp⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at success
      obtain ⟨fragment, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨tail, last, traversal, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨fragmentsSame, afterSame⟩ := (success_pure (fragment :: tail) fragments last after).mp final
      subst fragments
      subst after
      obtain ⟨middleValid, firstCarriers, firstFragment⟩ := step input (by simp) before fragment middle valid first
      obtain ⟨afterValid, tailCarriers, tailFragments⟩ := ih (fun input member => step input (by simp [member])) middle tail middleValid traversal
      refine ⟨afterValid, firstCarriers.trans tailCarriers, ?_⟩
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact firstFragment.preserve _ tailCarriers
      · exact tailFragments child member

/-- Actual mutual traversal preserves graph provenance and creates holes only for graph-bearing classes. -/
theorem enumeration_carriers (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment, Safe before → (∀ sc ∈ scs, sc.var < before.counter) → ReferencesCarry before →
      Success (enumerateNode graph fuel scs node) before fragment after →
      PreservesCarriers before after ∧ ReferencesCarry after ∧ FragmentCarries after fragment) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment, Safe before → (∀ sc ∈ scs, sc.var < before.counter) → ReferencesCarry before →
      Success (enumerateEdge graph fuel scs edge) before fragment after →
      PreservesCarriers before after ∧ ReferencesCarry after ∧ FragmentCarries after fragment) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment safe bounded carried success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                rw [terminal_branch graph fuel node scs first rest (by simp [view]) terminal] at success
                obtain ⟨root, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
                have mergeCarriers := mergeTerminal_carriers graph (fuel + 1) first rest before merged root safe.1.total merging
                have mergeReferences := references_transport before merged carried mergeCarriers
                  (mergeTerminal_origin graph (fuel + 1) first rest before merged root merging)
                  (mergeTerminal_obligations graph (fuel + 1) first rest before merged root merging)
                have mergeTotal := (mergeTerminal_valid graph (fuel + 1) first rest before merged root safe.1.total safe.2 merging).2
                obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
                cases ignored
                obtain ⟨restrictedCarriers, rootCarrier⟩ := mergeNode_carriers graph (fuel + 1) root node
                  (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie) merged restricted mergeTotal restriction
                have restrictedReferences := references_transport merged restricted mergeReferences restrictedCarriers
                  (mergeNode_origin graph (fuel + 1) root node _ merged restricted restriction)
                  (mergeNode_obligations graph (fuel + 1) root node _ merged restricted restriction)
                obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole root) fragment restricted after).mp final
                subst fragment
                subst after
                exact ⟨mergeCarriers.trans restrictedCarriers, restrictedReferences, fragmentCarries_hole restricted root rootCarrier⟩
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨_, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact ih.2 scs edge before after fragment safe bounded carried continued)
                | (obtain ⟨uv, allocatedState, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have exactState : uv = before.counter ∧ allocatedState = allocated (some node) before := by
                     simpa [Success, allocate_exact, ExceptT.run] using allocation
                   obtain ⟨uvSame, stateSame⟩ := exactState
                   subst uv
                   subst allocatedState
                   obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst fragment
                   subst after
                   have preserved := allocation_carriers (some node) before
                   have references := references_transport before _ carried preserved (allocation_origin (some node) before) rfl
                   have own : CarriesGraph (allocated (some node) before) before.counter := carries_self (allocated (some node) before) safe.1.total before.counter (.unenumerated (some node) [])
                     (by have alignment : before.counter = before.values.length := safe.1.aligned; simp [allocated, alignment]) trivial
                   exact ⟨preserved, references, fragmentCarries_hole _ _ own⟩)
      · intro scs edge before after fragment safe bounded carried success
        rw [edge_action graph fuel scs edge] at success
        obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp success
        cases ignored
        obtain ⟨_, same⟩ := (require_success _ before checked).mp required
        subst checked
        obtain ⟨added, suspended, suspension, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have suspensionExact : added = suspendedVars before.counter edge.equalities ∧ suspended = suspendedState edge.equalities.length before := by
          simpa [Success, suspendMany_exact, ExceptT.run] using suspension
        obtain ⟨addedSame, suspendedSame⟩ := suspensionExact
        subst added
        subst suspended
        obtain ⟨fragments, expanded, traversal, continued⟩ := (success_bind _ _ _ _ _).mp continued
        let inputs := scs ++ suspendedVars before.counter edge.equalities
        let limit := before.counter + edge.equalities.length
        have inputsBound : ∀ sc ∈ inputs, sc.var < limit := by
          intro sc member
          rcases List.mem_append.mp member with inherited | fresh
          · exact Nat.lt_of_lt_of_le (bounded sc inherited) (by dsimp [limit]; omega)
          · exact suspended_bounded before.counter edge.equalities sc fresh
        obtain ⟨expandedValid, expandedCarriers, childCarriers⟩ := mapM_carriers
          (fun entry : Nat × Nat => enumerateNode graph fuel (descendScs entry.2 inputs) entry.1)
          (fun state : State Symbol Guard => Safe state ∧ limit ≤ state.counter ∧ ReferencesCarry state) edge.children.zipIdx
          (by
            intro entry member previous output next previousValid execution
            have bounds : ∀ sc ∈ descendScs entry.2 inputs, sc.var < previous.counter :=
              fun sc member => Nat.lt_of_lt_of_le (descend_bounded limit entry.2 inputs inputsBound sc member) previousValid.2.1
            obtain ⟨nextSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ _ previous next output previousValid.1 bounds execution
            obtain ⟨preserved, references, fragment⟩ := ih.1 _ _ previous next output previousValid.1 bounds previousValid.2.2 execution
            exact ⟨⟨nextSafe, Nat.le_trans previousValid.2.1 growth, references⟩, preserved, fragment⟩)
          (suspendedState edge.equalities.length before) expanded fragments
          ⟨suspension_safe edge.equalities.length before safe, by rw [suspended_counter]; exact Nat.le_refl _, suspension_references edge.equalities.length before carried⟩ traversal
        have expandedFragment := fragmentCarries_node expanded edge.symbol fragments childCarriers
        obtain ⟨ignored, guarded, recording, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have guardedCarriers := recordResidual_carriers edge.residual (.node edge.symbol fragments) expanded guarded recording
        have guardedReferences := recordResidual_references edge.residual (.node edge.symbol fragments) expanded guarded expandedValid.2.2 expandedFragment recording
        obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.node edge.symbol fragments) fragment guarded after).mp final
        subst fragment
        subst after
        exact ⟨(suspension_carriers edge.equalities.length before).trans (expandedCarriers.trans guardedCarriers), guardedReferences,
          expandedFragment.preserve _ guardedCarriers⟩

end MicroCFTA.EnumerationGraphReferences
