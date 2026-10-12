import MicroCFTA.EnumerationCompleteness

/-!
# Constructing ordered node executions

Fresh equality witnesses extend the assignment only outside allocated storage.
Ordered child executions retain every earlier completed fragment.
-/

namespace MicroCFTA.EnumerationConstruction
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness

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

/-- One node action can construct the given term with only fresh assignment changes. -/
def Realizes (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop) (node : Nat) (term : Term Symbol) : Prop :=
  ∀ (before : State Symbol Guard) (assignment : Nat → Term Symbol) (scs : List Suspended), Safe before → ValidSuspended scs →
    (∀ sc ∈ scs, sc.var < before.counter) → InputsPending before scs →
    Satisfies (Accepted graph meaning) meaning assignment before →
    (∀ sc ∈ scs, Suspended.Holds assignment term sc) →
    ∃ fuel fragment after extended, Success (enumerateNode graph fuel scs node) before fragment after ∧
      Satisfies (Accepted graph meaning) meaning extended after ∧
      (∀ uv < before.counter, extended uv = assignment uv) ∧ fill extended fragment = term

/-- Assignment extension preserves every constraint whose variable is already allocated. -/
theorem holds_extension (before after : Nat → Term Symbol) (limit : Nat)
    (agree : ∀ uv < limit, after uv = before uv) (sc : Suspended) (bounded : sc.var < limit) (term : Term Symbol)
    (holds : Suspended.Holds before term sc) : Suspended.Holds after term sc := by
  intro path member
  simpa [agree sc.var bounded] using holds path member

/-- A child action preserves pending targets of every retained inherited constraint. -/
theorem retained_inputs_pending (graph : Graph Symbol Guard) (fuel node index : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (fragment : Fragment Symbol) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter) (pending : InputsPending before scs)
    (success : Success (enumerateNode graph fuel (descendScs index scs) node) before fragment after) : InputsPending after scs := by
  intro held storedFragment stored
  have old := (enumeration_origin graph fuel).1 (descendScs index scs) node before after fragment success held storedFragment stored
  obtain ⟨inside, root⟩ := enumerated_root before safe held storedFragment old
  have avoids := pending held storedFragment old
  have frame := (enumeration_protected graph fuel).1 (descendScs index scs) node held before after fragment
    safe inside root (descend_bounded before.counter index scs bounded) (descend_avoids _ held index scs avoids) success
  exact frame.avoids scs avoids

/-- Suspending classes leaves the existing equality forest unchanged. -/
theorem suspended_forest (count : Nat) (state : State Symbol Guard) :
    (suspendedState count state).representatives = state.representatives := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => exact ih (allocated none state)

/-- Inherited and fresh edge constraints both target pending classes after allocation. -/
theorem suspension_inputs_pending (state : State Symbol Guard) (safe : Safe state) (scs : List Suspended)
    (pending : InputsPending state scs) (tries : List EqualityTrie.Trie) :
    InputsPending (suspendedState tries.length state) (scs ++ suspendedVars state.counter tries) := by
  intro held fragment stored
  have old := suspension_origin tries.length state held fragment stored
  obtain ⟨inside, _⟩ := enumerated_root state safe held fragment old
  intro sc member same
  rw [suspended_forest] at same
  rcases List.mem_append.mp member with inherited | fresh
  · exact pending held fragment old sc inherited same
  · exact fresh_avoids state safe.1 held inside tries sc fresh same

/-- Each ordered child witness can be executed under one common bound and assignment extension. -/
theorem children_terminate (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (nodes : List Nat) (terms : List (Term Symbol)) (realizes : All₂ (Realizes graph meaning) nodes terms)
    (start : Nat) (scs : List Suspended) (before : State Symbol Guard) (assignment : Nat → Term Symbol)
    (safe : Safe before) (valid : ValidSuspended scs) (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (pending : InputsPending before scs) (satisfies : Satisfies (Accepted graph meaning) meaning assignment before)
    (holds : ∀ index term, terms[index]? = some term → ∀ sc ∈ descendScs (start + index) scs, Suspended.Holds assignment term sc) :
    ∃ fuel fragments after extended,
      Success ((nodes.zipIdx start).mapM fun entry => enumerateNode graph fuel (descendScs entry.2 scs) entry.1) before fragments after ∧
      Satisfies (Accepted graph meaning) meaning extended after ∧
      (∀ uv < before.counter, extended uv = assignment uv) ∧ fragments.map (fill extended) = terms := by
  induction realizes generalizing start before assignment with
  | nil => exact ⟨0, [], before, assignment, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, satisfies, by simp, rfl⟩
  | @cons node term nodes terms head tail ih =>
      have descendedBound := descend_bounded before.counter start scs bounded
      have descendedPending : InputsPending before (descendScs start scs) := by
        intro held fragment stored
        exact descend_avoids _ held start scs (pending held fragment stored)
      obtain ⟨firstFuel, fragment, middle, nextAssignment, first, middleSatisfies, firstAgree, firstTerm⟩ :=
        head before assignment (descendScs start scs) safe (descend_valid scs start valid) descendedBound descendedPending satisfies
          (by simpa using holds 0 term (by simp))
      obtain ⟨middleSafe, growth, fragmentBound⟩ := (enumeration_safety graph firstFuel).1 (descendScs start scs) node before middle fragment safe descendedBound first
      have middleBound : ∀ sc ∈ scs, sc.var < middle.counter := fun sc member => Nat.lt_of_lt_of_le (bounded sc member) growth
      have middlePending := retained_inputs_pending graph firstFuel node start scs before middle fragment safe bounded pending first
      have tailHolds : ∀ index child, terms[index]? = some child → ∀ sc ∈ descendScs (start + 1 + index) scs, Suspended.Holds nextAssignment child sc := by
        intro index child found sc member
        have original := holds (index + 1) child (by simpa using found) sc (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member)
        exact holds_extension assignment nextAssignment before.counter firstAgree sc
          (descend_bounded before.counter (start + 1 + index) scs bounded sc member) child original
      obtain ⟨restFuel, fragments, after, extended, continued, afterSatisfies, tailAgree, tailTerms⟩ :=
        ih (start + 1) middle nextAssignment middleSafe middleBound middlePending middleSatisfies tailHolds
      refine ⟨firstFuel + restFuel, fragment :: fragments, after, extended, ?_, afterSatisfies, ?_, ?_⟩
      · simp only [List.zipIdx_cons, List.mapM_cons]
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨fragment, middle, (enumeration_moreFuel graph firstFuel restFuel).1 (descendScs start scs) node before fragment middle first, ?_⟩
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨fragments, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        have more := retains_mapM _ _ (fun (entry : Nat × Nat) => (enumeration_moreFuel graph restFuel firstFuel).1 (descendScs entry.2 scs) entry.1)
          (nodes.zipIdx (start + 1)) _ _ _ continued
        simpa [Nat.add_comm] using more
      · intro uv inside
        exact (tailAgree uv (Nat.lt_of_lt_of_le inside growth)).trans (firstAgree uv inside)
      · simp only [List.map_cons, tailTerms]
        rw [fill_bounded middle.counter extended nextAssignment tailAgree fragment fragmentBound, firstTerm]

/-- Retaining one residual always has its exact finite state update. -/
theorem recordResidual_terminates (residual : Option Guard) (fragment : Fragment Symbol) (before : State Symbol Guard) :
    ∃ after, Success (recordResidual residual fragment) before () after := by
  cases residual with
  | none => exact ⟨before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
  | some guard => exact ⟨{before with obligations := (guard, fragment) :: before.obligations}, (modify_success _ _ _).mpr rfl⟩

/-- Fresh equality witnesses and ordered child executions construct the actual selected-edge action. -/
theorem edge_terminates (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (edge : EnumerationState.Edge Symbol Guard) (children : List (Term Symbol))
    (realizes : All₂ (Realizes graph meaning) edge.children children) (edgeValid : ValidEdge edge)
    (equalities : ∀ trie ∈ edge.equalities, EqualityHolds (.node edge.symbol children) trie)
    (residual : ResidualHolds meaning edge.residual (.node edge.symbol children))
    (before : State Symbol Guard) (assignment : Nat → Term Symbol) (scs : List Suspended)
    (safe : Safe before) (valid : ValidSuspended scs) (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (pending : InputsPending before scs) (satisfies : Satisfies (Accepted graph meaning) meaning assignment before)
    (holds : ∀ sc ∈ scs, Suspended.Holds assignment (.node edge.symbol children) sc) :
    ∃ fuel fragment after extended, Success (enumerateEdge graph fuel scs edge) before fragment after ∧
      Satisfies (Accepted graph meaning) meaning extended after ∧
      (∀ uv < before.counter, extended uv = assignment uv) ∧ fill extended fragment = .node edge.symbol children := by
  obtain ⟨witnesses, suspendedSatisfies, freshAgree, freshHolds⟩ := fresh_classes_state_complete (Accepted graph meaning) meaning
    before safe.1 assignment satisfies (.node edge.symbol children) edge.equalities equalities
  let suspended := suspendedState edge.equalities.length before
  let inputs := scs ++ suspendedVars before.counter edge.equalities
  have suspendedSafe : Safe suspended := suspension_safe edge.equalities.length before safe
  have inputsValid : ValidSuspended inputs := by
    intro sc member
    rcases List.mem_append.mp member with inherited | fresh
    · exact valid sc inherited
    · apply edgeValid.1 sc.trie
      rw [← suspendedVars_tries before.counter edge.equalities]
      exact List.mem_map.mpr ⟨sc, fresh, rfl⟩
  have inputsBound : ∀ sc ∈ inputs, sc.var < suspended.counter := by
    intro sc member
    rw [suspended_counter]
    rcases List.mem_append.mp member with inherited | fresh
    · exact Nat.lt_of_lt_of_le (bounded sc inherited) (by omega)
    · exact suspended_bounded before.counter edge.equalities sc fresh
  have inputsPending : InputsPending suspended inputs := suspension_inputs_pending before safe scs pending edge.equalities
  have inputsHold : ∀ sc ∈ inputs, Suspended.Holds witnesses (.node edge.symbol children) sc := by
    intro sc member
    rcases List.mem_append.mp member with inherited | fresh
    · exact holds_extension assignment witnesses before.counter freshAgree sc (bounded sc inherited) _ (holds sc inherited)
    · exact freshHolds sc fresh
  obtain ⟨childFuel, fragments, expanded, extended, traversal, expandedSatisfies, childAgree, childrenTerms⟩ :=
    children_terminate graph meaning edge.children children realizes 0 inputs suspended witnesses suspendedSafe inputsValid inputsBound inputsPending suspendedSatisfies
      (by simpa using suspended_descent_sound witnesses edge.symbol children inputs inputsValid inputsHold)
  have termSame : fill extended (.node edge.symbol fragments) = .node edge.symbol children := by simp [fill, childrenTerms]
  obtain ⟨after, recording⟩ := recordResidual_terminates edge.residual (.node edge.symbol fragments) expanded
  have afterSatisfies := (recordResidual_assignment (Accepted graph meaning) meaning extended edge.residual (.node edge.symbol fragments)
    expanded after recording).mpr ⟨expandedSatisfies, by simpa [termSame] using residual⟩
  have arity : arityAllows edge.children.length scs = true := by
    have sameLength : edge.children.length = children.length := realizes.length_eq
    rw [sameLength]
    exact suspended_arity_necessary assignment edge.symbol children scs holds
  refine ⟨childFuel + 1, .node edge.symbol fragments, after, extended, ?_, afterSatisfies, ?_, termSame⟩
  · rw [edge_action]
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨(), before, (require_success _ _ _).mpr ⟨arity, rfl⟩, ?_⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨suspendedVars before.counter edge.equalities, suspended, ?_, ?_⟩
    · simp [Success, suspendMany_exact, ExceptT.run, suspended]
    · exact (success_bind _ _ _ _ _).mpr ⟨fragments, expanded, traversal,
        (success_bind _ _ _ _ _).mpr ⟨(), after, recording, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩
  · intro uv inside
    exact (childAgree uv (by rw [suspended_counter]; omega)).trans (freshAgree uv inside)

/-- Pointwise child proofs can use membership in the complete child list. -/
theorem all₂_imp_mem (left : List α) (right : List β) (relation target : α → β → Prop)
    (related : All₂ relation left right) (step : ∀ a b, b ∈ right → relation a b → target a b) : All₂ target left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (step _ _ (by simp) head) (ih (fun a b member => step a b (by simp [member])))

/-- Every accepted finite term constructs a successful sufficiently bounded actual node action. -/
theorem enumerateNode_complete (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (node : Nat) (term : Term Symbol) (accepted : Accepted graph meaning node term) : Realizes graph meaning node term := by
  have realizeHeight : ∀ height, ∀ node term, term.height = height → Accepted graph meaning node term → Realizes graph meaning node term := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
        intro node term heightEq accepted before assignment scs safe valid bounded pending satisfies holds
        cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
        | cons first rest =>
            obtain ⟨fuel, root, after, success, afterSatisfies, assigned⟩ := enumerateNode_terminal_terminates graph meaning correct assignment
              before safe node term scs bounded pending satisfies accepted holds first rest terminal
            exact ⟨fuel, .hole root, after, assignment, success, afterSatisfies, by simp, by simpa [fill] using assigned⟩
        | nil =>
            cases accepted with
            | recursive node body term view inside => exact (complete.1 node body view).elim
            | edge node edges edge children view member childAccepted equalities residual =>
                have childRealizes : All₂ (Realizes graph meaning) edge.children children := by
                  apply all₂_imp_mem edge.children children (Accepted graph meaning) _ childAccepted
                  intro childNode child childMember childProof
                  have childBound := height_le_forestHeight children child childMember
                  have smaller : child.height < height := by
                    rw [← heightEq]
                    simp only [Term.height]
                    unfold forestHeight at childBound
                    omega
                  exact ih child.height smaller childNode child rfl childProof
                obtain ⟨fuel, fragment, after, extended, execution, afterSatisfies, agree, exactTerm⟩ := edge_terminates graph meaning edge children
                  childRealizes (complete.2 node edges view edge member) equalities residual before assignment scs safe valid bounded pending satisfies holds
                refine ⟨fuel + 1, fragment, after, extended, ?_, afterSatisfies, agree, exactTerm⟩
                simp only [enumerateNode, view, terminal]
                exact (success_bind _ _ _ _ _).mpr ⟨edge, before, (choose_success _ _ _ _).mpr ⟨member, rfl⟩, execution⟩
  exact realizeHeight term.height node term rfl accepted

end MicroCFTA.EnumerationConstruction
