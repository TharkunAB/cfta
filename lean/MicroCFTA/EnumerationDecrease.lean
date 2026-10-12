import MicroCFTA.EnumerationOutConstruction

/-!
# Term-height decrease of pending graph work

Terminal merges change only variables assigned the reached term.
Child traversal can therefore create graph work only at smaller terms.
-/

namespace MicroCFTA.EnumerationDecrease
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction EnumerationOutConstruction

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

/-- One concrete slot still carries a graph node that must be expanded. -/
def GraphPending (state : State Symbol Guard) (uv : Nat) : Prop :=
  ∃ node scs, state.values[uv]? = some (.unenumerated (some node) scs)

/-- Every large pending term after an action occupied the same pending index before it. -/
def HighOrigin (assignment : Nat → Term Symbol) (height : Nat) (before after : State Symbol Guard) : Prop :=
  ∀ uv, height ≤ (assignment uv).height → GraphPending after uv → GraphPending before uv

/-- Larger cutoffs retain the same pending-origin implication. -/
theorem HighOrigin.weaken (origin : HighOrigin assignment small before after) (larger : small ≤ large) :
    HighOrigin assignment large before after := fun uv high pending => origin uv (Nat.le_trans larger high) pending

/-- Pending-origin implications compose across ordered actions. -/
theorem HighOrigin.trans (first : HighOrigin assignment height before middle) (second : HighOrigin assignment height middle after) :
    HighOrigin assignment height before after := fun uv high pending => first uv high (second uv high pending)

/-- Terminal class merging leaves slots with a different assigned term unchanged. -/
theorem mergeTerminal_unequal_frame (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (correct : IntersectionCorrect graph (Accepted graph meaning)) (assignment : Nat → Term Symbol)
    (fuel : Nat) (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard) (target held : Nat)
    (total : UnionFind.Total before.representatives)
    (success : Success (mergeTerminal graph fuel first rest) before target after)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after)
    (different : assignment held ≠ assignment target) : after.values[held]? = before.values[held]? := by
  obtain ⟨beforeSatisfies, equalOriginal⟩ := mergeTerminal_backward graph (Accepted graph meaning) correct meaning assignment fuel first rest before after target total success satisfies
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest) before scanned recorded ⟨rfl, paths⟩ scan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have joined := terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
    (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, _⟩ := merging_representative before.values roots _ fuel first.var winner united resolved joined resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨targetSame, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst target
  subst after
  have separate : winner ≠ held := by intro same; exact different (congrArg assignment same.symm)
  have absent : held ∉ recorded := by
    intro member
    rw [recordedSame] at member
    obtain ⟨sc, present, same⟩ := List.mem_map.mp member
    obtain ⟨size, path⟩ := paths sc.var
    have toRoot := beforeSatisfies.1.1 sc.var (roots sc.var) (UnionFind.sameClass_root path)
    exact different (by rw [← same, ← toRoot]; exact (equalOriginal sc present).symm)
  exact (terminal_assimilations_frame graph winner held recorded resolved assimilated (Ne.symm separate) absent assimilation).trans
    (by rw [resolvedValid.values])

/-- A terminal node branch leaves every differently assigned slot unchanged. -/
theorem terminal_unequal_frame (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (correct : IntersectionCorrect graph (Accepted graph meaning)) (assignment : Nat → Term Symbol)
    (fuel node held : Nat) (scs : List Suspended) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (nonempty : graph.node node ≠ .empty) (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after)
    (different : assignment held ≠ fill assignment fragment) : after.values[held]? = before.values[held]? := by
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨mergedLive, mergedTotal⟩ := mergeTerminal_valid graph (fuel + 1) first rest before merged root safe.1.total safe.2 merging
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst fragment
  subst after
  have mergedSatisfies := ((mergeNode_assignment graph (Accepted graph meaning) correct meaning assignment (fuel + 1) root node
    (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie) merged restricted mergedTotal restriction).mp satisfies).1
  have separate : ¬UnionFind.SameClass merged.representatives held root := by
    intro related
    exact different (by simpa [fill] using mergedSatisfies.1.1 held root related)
  have unchanged := (mergeNode_live graph (fuel + 1) root node (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie)
    merged restricted mergedTotal mergedLive restriction).2.2.2.2.1 held separate
  exact unchanged.trans (mergeTerminal_unequal_frame graph meaning correct assignment (fuel + 1) first rest before merged root held safe.1.total merging
    mergedSatisfies (by simpa [fill] using different))

/-- Fresh equality slots cannot introduce graph work. -/
theorem allocation_graph_origin (state : State Symbol Guard) (uv : Nat) (pending : GraphPending (allocated none state) uv) : GraphPending state uv := by
  obtain ⟨node, scs, stored⟩ := pending
  by_cases inside : uv < state.values.length
  · exact ⟨node, scs, by simpa [allocated, List.getElem?_append, inside] using stored⟩
  · simp only [allocated, List.getElem?_append, ite_eq_right inside] at stored
    cases difference : uv - state.values.length <;> simp [difference] at stored

/-- The complete fresh-class batch cannot introduce graph work. -/
theorem suspension_graph_origin (count : Nat) (state : State Symbol Guard) (uv : Nat)
    (pending : GraphPending (suspendedState count state) uv) : GraphPending state uv := by
  induction count generalizing state with
  | zero => exact pending
  | succ count ih => exact allocation_graph_origin state uv (ih (allocated none state) pending)

/-- Ordered traversal composes backward assignments and origins above every child height. -/
theorem mapM_height_origin (action : α → EnumerateM Symbol Guard (Fragment Symbol))
    (invariant : State Symbol Guard → Prop) (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (inputs : List α)
    (step : ∀ input ∈ inputs, ∀ before fragment after, invariant before → Success (action input) before fragment after →
      invariant after ∧ (Satisfies language meaning assignment after → Satisfies language meaning assignment before ∧
        HighOrigin assignment ((fill assignment fragment).height + 1) before after))
    (before after : State Symbol Guard) (fragments : List (Fragment Symbol)) (height : Nat)
    (valid : invariant before) (success : Success (inputs.mapM action) before fragments after)
    (satisfies : Satisfies language meaning assignment after)
    (below : ∀ fragment ∈ fragments, (fill assignment fragment).height < height) :
    Satisfies language meaning assignment before ∧ HighOrigin assignment height before after := by
  induction inputs generalizing before fragments with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] fragments before after).mp success
      exact ⟨satisfies, fun _ _ pending => pending⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at success
      obtain ⟨fragment, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨fragmentsSame, afterSame⟩ := (success_pure (fragment :: tail) fragments last after).mp final
      subst fragments
      subst after
      obtain ⟨middleValid, firstBackward⟩ := step input (by simp) before fragment middle valid first
      obtain ⟨middleSatisfies, tailOrigin⟩ := ih (fun input member => step input (by simp [member])) middle tail middleValid remaining
        (fun fragment member => below fragment (by simp [member]))
      obtain ⟨beforeSatisfies, firstOrigin⟩ := firstBackward middleSatisfies
      exact ⟨beforeSatisfies, (firstOrigin.weaken (below fragment (by simp))).trans tailOrigin⟩

/-- Recording a residual leaves the value array unchanged. -/
theorem recordResidual_values (residual : Option Guard) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (success : Success (recordResidual residual fragment) before () after) : after.values = before.values := by
  cases residual with
  | none => exact congrArg State.values ((success_pure () () before after).mp success).2
  | some guard => rw [(modify_success _ before after).mp success]

/-- Node traversal creates no larger pending term; an edge creates only strictly smaller pending terms. -/
theorem enumeration_height_origin (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment, Safe before →
      (∀ sc ∈ scs, sc.var < before.counter) → ValidSuspended scs →
      Success (enumerateNode graph fuel scs node) before fragment after →
      Satisfies (Accepted graph meaning) meaning assignment after →
      HighOrigin assignment ((fill assignment fragment).height + 1) before after) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment, Safe before →
      (∀ sc ∈ scs, sc.var < before.counter) → ValidSuspended scs → ValidEdge edge →
      Success (enumerateEdge graph fuel scs edge) before fragment after →
      Satisfies (Accepted graph meaning) meaning assignment after →
      HighOrigin assignment (fill assignment fragment).height before after) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment _ _ _ success _
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment _ _ _ _ success _
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment safe bounded valid success satisfies
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | recursive body => exact (complete.1 node body view).elim
        | alternatives edges | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                intro held high pending
                have different : assignment held ≠ fill assignment fragment := by
                  intro same
                  have eqHeight := congrArg Term.height same
                  omega
                have same := terminal_unequal_frame graph meaning correct assignment fuel node held scs first rest before after fragment safe
                  (by simp [view]) terminal success satisfies different
                obtain ⟨pendingNode, pendingScs, stored⟩ := pending
                exact ⟨pendingNode, pendingScs, same ▸ stored⟩
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨selected, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact (ih.2 scs edge before after fragment safe bounded valid (complete.2 node edges view edge selected) continued satisfies).weaken (by omega))
      · intro scs edge before after fragment safe bounded valid edgeValid success satisfies
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
        obtain ⟨ignored, guarded, recording, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.node edge.symbol fragments) fragment guarded after).mp final
        subst fragment
        subst after
        have expandedSatisfies := ((recordResidual_assignment (Accepted graph meaning) meaning assignment edge.residual (.node edge.symbol fragments)
          expanded guarded recording).mp satisfies).1
        let inputs := scs ++ suspendedVars before.counter edge.equalities
        let limit := before.counter + edge.equalities.length
        have inputsValid : ValidSuspended inputs := by
          intro sc member
          rcases List.mem_append.mp member with inherited | fresh
          · exact valid sc inherited
          · apply edgeValid.1 sc.trie
            rw [← suspendedVars_tries before.counter edge.equalities]
            exact List.mem_map.mpr ⟨sc, fresh, rfl⟩
        have inputsBound : ∀ sc ∈ inputs, sc.var < limit := by
          intro sc member
          rcases List.mem_append.mp member with inherited | fresh
          · exact Nat.lt_of_lt_of_le (bounded sc inherited) (by dsimp [limit]; omega)
          · exact suspended_bounded before.counter edge.equalities sc fresh
        have initialValid : Safe (suspendedState edge.equalities.length before) ∧ limit ≤ (suspendedState edge.equalities.length before).counter :=
          ⟨suspension_safe edge.equalities.length before safe, by rw [suspended_counter]; exact Nat.le_refl _⟩
        obtain ⟨_, origin⟩ := mapM_height_origin
          (fun entry : Nat × Nat => enumerateNode graph fuel (descendScs entry.2 inputs) entry.1)
          (fun state : State Symbol Guard => Safe state ∧ limit ≤ state.counter) (Accepted graph meaning) meaning assignment edge.children.zipIdx
          (by
            intro entry member previous output next previousValid execution
            have childBound : ∀ sc ∈ descendScs entry.2 inputs, sc.var < previous.counter :=
              fun sc member => Nat.lt_of_lt_of_le (descend_bounded limit entry.2 inputs inputsBound sc member) previousValid.2
            obtain ⟨nextSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ _ previous next output previousValid.1 childBound execution
            refine ⟨⟨nextSafe, Nat.le_trans previousValid.2 growth⟩, ?_⟩
            intro nextSatisfies
            exact ⟨((enumeration_backward graph meaning complete correct assignment fuel).1 _ _ previous next output previousValid.1 childBound
              (descend_valid inputs entry.2 inputsValid) execution nextSatisfies).1,
              ih.1 _ _ previous next output previousValid.1 childBound (descend_valid inputs entry.2 inputsValid) execution nextSatisfies⟩)
          (suspendedState edge.equalities.length before) expanded fragments (fill assignment (.node edge.symbol fragments)).height initialValid traversal expandedSatisfies
          (by
            intro child member
            have bound := height_le_forestHeight (fragments.map (fill assignment)) (fill assignment child) (List.mem_map.mpr ⟨child, member, rfl⟩)
            simp only [fill, Term.height]
            unfold forestHeight at bound
            omega)
        intro uv high pending
        have expandedPending : GraphPending expanded uv := by
          obtain ⟨node, scs, stored⟩ := pending
          exact ⟨node, scs, by simpa [recordResidual_values edge.residual (.node edge.symbol fragments) expanded guarded recording] using stored⟩
        exact suspension_graph_origin edge.equalities.length before uv (origin uv high expandedPending)

/-- A node with no reached terminal constraint creates only smaller pending terms. -/
theorem nonterminal_height_origin (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (fuel node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter) (valid : ValidSuspended scs)
    (nonterminal : ∀ sc ∈ scs, EqualityTrie.isTerminal sc.trie = false)
    (success : Success (enumerateNode graph fuel scs node) before fragment after)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after) :
    HighOrigin assignment (fill assignment fragment).height before after := by
  cases fuel with
  | zero => exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel =>
      have terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro sc member
        simp [nonterminal sc member]
      cases view : graph.node node with
      | empty =>
          have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
          exact (reject_unsuccessful before after fragment impossible).elim
      | recursive body => exact (complete.1 node body view).elim
      | unresolved reference =>
          simp only [enumerateNode, view, terminal] at success
          exact (success_failure .unresolvedReference before after fragment success).elim
      | alternatives edges =>
          simp only [enumerateNode, view, terminal] at success
          obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨selected, same⟩ := (choose_success _ before middle edge).mp choice
          subst middle
          exact (enumeration_height_origin graph meaning complete correct assignment fuel).2 scs edge before after fragment safe bounded valid
            (complete.2 node edges view edge selected) continued satisfies

/-- Selected-root expansion removes its own pending work and creates no work at that height or above. -/
theorem enumerateOut_height_origin (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (fuel uv : Nat) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (ready : Ready uv before) (proper : ProperState before)
    (success : Success (enumerateOut graph fuel uv) before fragment after)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after) :
    HighOrigin assignment (assignment uv).height before after ∧ ¬GraphPending after uv := by
  have canonical := proper_canonical before proper
  obtain ⟨beforeSatisfies, equation⟩ := enumerateOut_backward graph meaning complete correct assignment fuel uv before after fragment ready
    (fun node scs stored => canonical _ (List.mem_of_getElem? stored)) success satisfies
  unfold enumerateOut at success
  obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readSafe, readCounter, readFrame, stored⟩ := getValue_root (fuel + 1) uv before readState value ready.safe ready.inside ready.root reading
  have readStable := (getValue_storage (fuel + 1) uv before readState value ready.safe ready.inside reading).1
  cases value with
  | eliminated | enumerated _ => exact (reject_unsuccessful readState after fragment continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful readState after fragment continued).elim
      | some node =>
          obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨selectedSame, resolvedSafe, resolvedCounter, resolvedFrame⟩ := representative_root (fuel + 1) uv selected readState resolved readSafe
            (by simpa [readCounter] using ready.inside) readFrame.root resolution
          subst selected
          have resolvedStable := representative_read (fuel + 1) uv uv readState resolved readSafe (by simpa [readCounter] using ready.inside) resolution
          obtain ⟨current, currentState, currentRead, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨currentSame, currentStateSame⟩ := (get_success resolved currentState current).mp currentRead
          subst current
          subst currentState
          obtain ⟨ignored, started, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ resolved started).mp bookkeeping
          obtain ⟨produced, expanded, expansion, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have oldStored : before.values[uv]? = some (.unenumerated (some node) scs) := readFrame.value ▸ stored
          have bounded : ∀ sc ∈ scs, sc.var < resolved.counter := by
            have bounds := ready.safe.1.values _ (List.mem_of_getElem? oldStored)
            simpa [resolvedCounter, readCounter, SlotBound] using bounds
          have frame := readFrame.trans resolvedFrame
          have separate := frame.avoids scs (ready.avoids node scs oldStored)
          let ancestry := match graph.node node with
            | .recursive _ => (recursionKey node scs :: resolved.recursionAncestry uv).eraseDups
            | _ => resolved.recursionAncestry uv
          have startedSafe := ancestry_safe resolved ancestry resolvedSafe
          obtain ⟨expandedSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ _ _ expanded produced startedSafe bounded expansion
          have expandedFrame := (enumeration_protected graph fuel).1 _ _ uv _ expanded produced startedSafe
            (by simpa [resolvedCounter, readCounter] using ready.inside) resolvedFrame.root bounded separate expansion
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ expanded cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ _ written).mp writing
          obtain ⟨fragmentSame, afterSame⟩ := (success_pure produced fragment _ after).mp final
          subst fragment
          subst after
          have expandedStored : expanded.values[uv]? = some (.unenumerated (some node) scs) := expandedFrame.value.trans (resolvedFrame.value.trans stored)
          have selectedRestriction : slotSatisfies assignment uv (heap (Accepted graph meaning) expanded.values uv) := by
            simpa [heap, expandedStored] using stored_satisfies (Accepted graph meaning) meaning assignment before beforeSatisfies uv _ oldStored
          have neutral := neutralize_satisfies (Accepted graph meaning) meaning assignment uv _ satisfies
          rw [neutralize_overwrite] at neutral
          have expandedSatisfies : Satisfies (Accepted graph meaning) meaning assignment expanded :=
            neutralize_restore (Accepted graph meaning) meaning assignment uv _ neutral selectedRestriction
          have nonterminal : ∀ sc ∈ scs, EqualityTrie.isTerminal sc.trie = false :=
            fun sc member => (proper _ (List.mem_of_getElem? oldStored) sc member).2.2
          have origin := nonterminal_height_origin graph meaning complete correct assignment fuel _ scs _ expanded produced startedSafe bounded
            (canonical _ (List.mem_of_getElem? oldStored)) nonterminal expansion expandedSatisfies
          have inside : uv < expanded.values.length := (List.getElem?_eq_some_iff.mp expandedStored).1
          have removed : ¬GraphPending {expanded with expansionAncestry := [], values := expanded.values.set uv (.enumerated produced)} uv := by
            rintro ⟨pendingNode, pendingScs, found⟩
            simp [inside] at found
          refine ⟨?_, removed⟩
          intro held high pending
          have different : held ≠ uv := by intro same; subst held; exact removed pending
          obtain ⟨pendingNode, pendingScs, found⟩ := pending
          have inExpanded : GraphPending expanded held := ⟨pendingNode, pendingScs, by simpa [Ne.symm different] using found⟩
          obtain ⟨oldNode, oldScs, oldSlot⟩ := origin held (by simpa [equation] using high) inExpanded
          exact ⟨oldNode, oldScs, by simpa [resolvedStable.values, readStable.values] using oldSlot⟩

end MicroCFTA.EnumerationDecrease
