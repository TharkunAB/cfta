import MicroCFTA.EnumerationSemantics

/-!
# Independence from the selected root payload

The selected root has no incoming suspended reference. Child enumeration can
therefore replace its old payload with a neutral pending slot. This permits
the final write proof to establish the old node restriction without assuming
that restriction during its own expansion.
-/

namespace MicroCFTA.EnumerationFrame
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics

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

/-- Remove the selected payload restriction while retaining its live root slot. -/
def neutralize (held : Nat) (state : State Symbol Guard) : State Symbol Guard :=
  {state with values := state.values.set held (.unenumerated none [])}

/-- Every other raw slot retains its original value. -/
theorem neutralize_read (held uv : Nat) (state : State Symbol Guard) (different : uv ≠ held) :
    (neutralize held state).values[uv]? = state.values[uv]? := by
  simp [neutralize, Ne.symm different]

/-- Neutralizing a live root retains both reachable-state safety invariants. -/
theorem neutralize_safe (held : Nat) (state : State Symbol Guard) (safe : Safe state)
    (root : IsRoot state.representatives held) : Safe (neutralize held state) := by
  exact (setValue_safe held (.unenumerated none []) state (neutralize held state) safe root (by simp)
    (by simp [SlotBound]) ((modify_success _ state _).mpr rfl)).1

/-- Consecutive writes to distinct payload slots commute. -/
theorem neutralize_set (held uv : Nat) (state : State Symbol Guard) (value : UVarValue Symbol) (different : uv ≠ held) :
    neutralize held {state with values := state.values.set uv value} =
      {neutralize held state with values := (neutralize held state).values.set uv value} := by
  unfold neutralize
  congr 1
  exact List.set_comm value (.unenumerated none []) different

/-- Fresh allocation commutes with removal of an older payload restriction. -/
theorem neutralize_allocated (held : Nat) (node : Option Nat) (state : State Symbol Guard)
    (inside : held < state.values.length) :
    neutralize held (allocated node state) = allocated node (neutralize held state) := by
  unfold neutralize allocated
  congr 1
  exact List.set_append_left held _ inside

/-- An unrelated raw read has the same successful result with a neutral root. -/
theorem rawValue_neutral (held uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (different : uv ≠ held) (success : Success (rawValue uv) before value after) :
    Success (rawValue uv) (neutralize held before) value (neutralize held after) := by
  obtain ⟨stored, same⟩ := (rawValue_success uv before after value).mp success
  subst after
  exact (rawValue_success uv _ _ value).mpr ⟨by rw [neutralize_read held uv before different]; exact stored, rfl⟩

/-- Representative lookup is independent of every payload value. -/
theorem representative_neutral (held fuel uv root : Nat) (before after : State Symbol Guard)
    (success : Success (representative fuel uv) before root after) :
    Success (representative fuel uv) (neutralize held before) root (neutralize held after) := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact (representative_success fuel uv _ _ found.representative).mpr ⟨found, lookup, rfl, rfl⟩

/-- Union depends only on the forest and is independent of payload values. -/
theorem unionVariables_neutral (held fuel left right : Nat) (before after : State Symbol Guard)
    (success : Success (unionVariables fuel left right) before () after) :
    Success (unionVariables fuel left right) (neutralize held before) () (neutralize held after) := by
  obtain ⟨forest, result, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact (unionVariables_success fuel left right _ _).mpr ⟨forest, result, rfl⟩

/-- An unrelated payload write commutes with neutralization. -/
theorem setValue_neutral (held uv : Nat) (value : UVarValue Symbol) (before after : State Symbol Guard)
    (different : uv ≠ held) (success : Success (setValue uv value) before () after) :
    Success (setValue uv value) (neutralize held before) () (neutralize held after) := by
  obtain rfl := (modify_success _ before after).mp success
  exact (modify_success _ _ _).mpr (neutralize_set held uv before value different)

/-- Fresh allocation has the same new identifier after neutralization. -/
theorem allocate_neutral (held : Nat) (node : Option Nat) (before after : State Symbol Guard) (uv : Nat)
    (inside : held < before.values.length) (success : Success (allocate node) before uv after) :
    Success (allocate node) (neutralize held before) uv (neutralize held after) := by
  have exactState : uv = before.counter ∧ after = allocated node before := by simpa [Success, allocate_exact, ExceptT.run] using success
  obtain ⟨rfl, rfl⟩ := exactState
  rw [neutralize_allocated held node before inside]
  simp [Success, allocate_exact, ExceptT.run, neutralize]

/-- Successful pending assimilation does not inspect or change a separate payload. -/
theorem assimilate_neutral (graph : Graph Symbol Guard) (held target source : Nat) (before after : State Symbol Guard)
    (targetOther : target ≠ held) (sourceOther : source ≠ held)
    (success : Success (EnumerationState.assimilate graph target source) before () after) :
    Success (EnumerationState.assimilate graph target source) (neutralize held before) () (neutralize held after) := by
  have original := success
  by_cases same : target = source
  · subst source
    have unchanged : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    subst after
    simp [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run]
  · simp only [EnumerationState.assimilate, same, ↓reduceIte] at success
    obtain ⟨sourceValue, readSource, readingSource, continued⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨sourceRead, sourceStateSame⟩ := (rawValue_success source before readSource sourceValue).mp readingSource
    subst readSource
    have sourceNeutral : (neutralize held before).values[source]? = some sourceValue := by
      rw [neutralize_read held source before sourceOther]
      exact sourceRead
    cases sourceValue with
    | eliminated =>
        obtain ⟨_, unchanged⟩ := (success_pure () () before after).mp continued
        subst after
        simp [Success, EnumerationState.assimilate, same, rawValue, sourceNeutral,
          bind, get, getThe, MonadStateOf.get, pure, StateT.bind, StateT.pure, StateT.get,
          ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
    | enumerated fragment =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨_, targetStateSame⟩ := (rawValue_success target before readTarget targetValue).mp readingTarget
        subst readTarget
        exact (success_failure .invalidIntersection before after () continued).elim
    | unenumerated sourceNode sourceScs =>
        obtain ⟨targetValue, readTarget, readingTarget, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨targetRead, targetStateSame⟩ := (rawValue_success target before readTarget targetValue).mp readingTarget
        subst readTarget
        have targetNeutral : (neutralize held before).values[target]? = some targetValue := by
          rw [neutralize_read held target before targetOther]
          exact targetRead
        cases targetValue with
        | eliminated | enumerated _ => exact (success_failure .invalidIntersection before after () continued).elim
        | unenumerated targetNode targetScs =>
            let merged : UVarValue Symbol := .unenumerated (match sourceNode, targetNode with
              | none, node => node | node, none => node | some left, some right => some (graph.intersect left right))
              (sourceScs ++ targetScs)
            have intersection : intersectValues graph (.unenumerated sourceNode sourceScs)
                (.unenumerated targetNode targetScs) = some merged := by cases sourceNode <;> cases targetNode <;> rfl
            have notEmpty : hasEmptyContents graph merged = false := by
              simp only [intersection] at continued
              obtain ⟨ignored, checked, required, _⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              simpa using ((require_success _ before checked).mp required).1
            have exactAction := assimilate_exact graph before target source sourceNode targetNode sourceScs targetScs
              merged same sourceRead targetRead intersection notEmpty
            have exactState : after = assimilated before target source merged := by simpa [Success, exactAction, ExceptT.run] using original
            rw [exactState]
            have commute : neutralize held (assimilated before target source merged) =
                assimilated (neutralize held before) target source merged := by
              unfold neutralize assimilated
              congr 1
              dsimp only
              rw [List.set_comm (UVarValue.eliminated : UVarValue Symbol) (.unenumerated none []) sourceOther,
                List.set_comm merged (.unenumerated none []) targetOther]
            rw [commute]
            simp [Success, assimilate_exact graph (neutralize held before) target source sourceNode targetNode sourceScs targetScs
              merged same sourceNeutral targetNeutral intersection notEmpty, ExceptT.run]

/-- Source node restriction commutes with neutralization of a separate class. -/
theorem mergeNode_neutral (graph : Graph Symbol Guard) (held fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (separate : ¬UnionFind.SameClass before.representatives held uv)
    (success : Success (mergeNode graph fuel uv node scs) before () after) :
    Success (mergeNode graph fuel uv node scs) (neutralize held before) () (neutralize held after) := by
  cases lookup : UnionFind.findRoot fuel before.representatives uv with
  | none =>
      simp [Success, mergeNode, representative, lookup, EnumerationState.failure, bind, get, getThe, MonadStateOf.get,
        pure, StateT.bind, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
  | some found =>
      have different := representative_away before.representatives fuel uv held separate found lookup
      cases stored : before.values[found.representative]? with
      | none =>
          simp [Success, mergeNode, representative, lookup, rawValue, stored, EnumerationState.failure,
            bind, get, getThe, MonadStateOf.get, set, pure, StateT.bind, StateT.pure, StateT.get, StateT.set,
            ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
      | some previous =>
          cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
          | none =>
              simp [Success, mergeNode, representative, lookup, rawValue, stored, intersection, EnumerationState.failure,
                bind, get, getThe, MonadStateOf.get, set, pure, StateT.bind, StateT.pure, StateT.get, StateT.set,
                ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
          | some merged =>
              cases empty : hasEmptyContents graph merged with
              | true =>
                  simp [Success, mergeNode, representative, lookup, rawValue, stored, intersection, empty, require, reject,
                    setValue, inheritAncestry, bind, get, getThe, MonadStateOf.get, set, pure, modify, modifyGet,
                    MonadStateOf.modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.set, StateT.modifyGet,
                    ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
              | false =>
                  have execution := mergeNode_exact graph before fuel uv node scs found previous merged lookup stored intersection empty
                  have same : after = nodeMerged before found merged := by simpa [Success, execution, ExceptT.run] using success
                  rw [same]
                  have commute : neutralize held (nodeMerged before found merged) = nodeMerged (neutralize held before) found merged := by
                    unfold neutralize nodeMerged
                    congr 1
                    exact List.set_comm merged (.unenumerated none []) different
                  have storedNeutral : (neutralize held before).values[found.representative]? = some previous := by
                    rw [neutralize_read held found.representative before different]
                    exact stored
                  rw [commute]
                  simp [Success, mergeNode_exact graph (neutralize held before) fuel uv node scs found previous merged
                    lookup storedNeutral intersection empty, ExceptT.run]

/-- A mapped traversal transports each successful branch under a fixed state transformation. -/
theorem mapM_transport (action : α → EnumerateM Symbol Guard β) (transform : State Symbol Guard → State Symbol Guard)
    (invariant : State Symbol Guard → Prop) (inputs : List α)
    (step : ∀ input ∈ inputs, ∀ before output after, invariant before → Success (action input) before output after →
      invariant after ∧ Success (action input) (transform before) output (transform after))
    (before after : State Symbol Guard) (outputs : List β) (valid : invariant before)
    (success : Success (inputs.mapM action) before outputs after) :
    Success (inputs.mapM action) (transform before) outputs (transform after) := by
  induction inputs generalizing before outputs with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] outputs before after).mp success
      exact (success_pure [] [] _ _).mpr ⟨rfl, rfl⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at success ⊢
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨middleValid, firstMoved⟩ := step input (by simp) before output middle valid first
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨outputsSame, afterSame⟩ := (success_pure (output :: tail) outputs last after).mp final
      subst outputs
      subst after
      exact (success_bind _ _ _ _ _).mpr ⟨output, transform middle, firstMoved,
        (success_bind _ _ _ _ _).mpr ⟨tail, transform last,
          ih (fun input member => step input (List.mem_cons_of_mem _ member)) middle tail middleValid remaining,
          (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩

/-- A source loop transports each successful branch under a fixed state transformation. -/
theorem forM_transport (action : α → EnumerateM Symbol Guard Unit) (transform : State Symbol Guard → State Symbol Guard)
    (inputs : List α)
    (step : ∀ input ∈ inputs, ∀ before after, Success (action input) before () after →
      Success (action input) (transform before) () (transform after))
    (before after : State Symbol Guard) (success : Success (inputs.forM action) before () after) :
    Success (inputs.forM action) (transform before) () (transform after) := by
  induction inputs generalizing before with
  | nil =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact (success_pure () () _ _).mpr ⟨rfl, rfl⟩
  | cons input rest ih =>
      change Success (action input >>= fun _ => rest.forM action) before () after at success
      change Success (action input >>= fun _ => rest.forM action) (transform before) () (transform after)
      obtain ⟨ignored, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      cases ignored
      exact (success_bind _ _ _ _ _).mpr ⟨(), transform middle, step input (by simp) before middle first,
        ih (fun input member => step input (List.mem_cons_of_mem _ member)) middle continued⟩

/-- The complete terminal merge is independent of a separate protected root payload. -/
theorem mergeTerminal_neutral (graph : Graph Symbol Guard) (held fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (total : UnionFind.Total before.representatives)
    (root : IsRoot before.representatives held) (avoids : Avoids before.representatives held (first :: rest))
    (success : Success (mergeTerminal graph fuel first rest) before target after) :
    Success (mergeTerminal graph fuel first rest) (neutralize held before) target (neutralize held after) := by
  have frame := mergeTerminal_protected graph fuel first rest held before after target total root avoids success
  have targetOther : target ≠ held := by
    intro same
    apply frame.2.2.1
    rw [same]
    exact UnionFind.sameClass_root frame.2.1.choose_spec
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold mergeTerminal at success ⊢
  obtain ⟨recorded, scanned, preScan, continued⟩ := (success_bind _ _ _ _ _).mp success
  have recordedSame := (representatives_scan before.values roots fuel (first :: rest) before scanned recorded ⟨rfl, paths⟩ preScan).2
  have scanMoved := mapM_transport (fun sc => representative fuel sc.var) (neutralize held) (fun _ => True) (first :: rest)
    (fun sc _ previous result next _ step => ⟨trivial, representative_neutral held fuel sc.var result previous next step⟩)
    before scanned recorded trivial preScan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unionsMoved := forM_transport (fun sc => unionVariables fuel first.var sc.var) (neutralize held) rest
    (fun sc _ previous next step => unionVariables_neutral held fuel first.var sc.var previous next step) scanned united unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have resolutionMoved := representative_neutral held fuel first.var winner united resolved resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨targetSame, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst target
  subst after
  have sourceOther : ∀ source ∈ recorded, source ≠ held := by
    intro source member same
    rw [recordedSame] at member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨size, path⟩ := paths sc.var
    apply avoids sc present
    exact UnionFind.sameClass_symm (by simpa [same] using UnionFind.sameClass_root path)
  have assimilationMoved := forM_transport (EnumerationState.assimilate graph winner) (neutralize held) recorded
    (fun source member previous next step => assimilate_neutral graph held winner source previous next targetOther (sourceOther source member) step)
    resolved assimilated assimilation
  exact (success_bind _ _ _ _ _).mpr ⟨recorded, neutralize held scanned, scanMoved,
    (success_bind _ _ _ _ _).mpr ⟨(), neutralize held united, unionsMoved,
      (success_bind _ _ _ _ _).mpr ⟨winner, neutralize held resolved, resolutionMoved,
        (success_bind _ _ _ _ _).mpr ⟨(), neutralize held assimilated, assimilationMoved,
          (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩⟩⟩

/-- The complete terminal node branch does not inspect its separate protected payload. -/
theorem enumerateNode_terminal_neutral (graph : Graph Symbol Guard) (held fuel node : Nat)
    (scs : List Suspended) (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard)
    (fragment : Fragment Symbol) (safe : Safe before) (root : IsRoot before.representatives held)
    (avoids : Avoids before.representatives held scs) (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) :
    Success (enumerateNode graph (fuel + 1) scs node) (neutralize held before) fragment (neutralize held after) := by
  have selectedAvoid : Avoids before.representatives held (first :: rest) := by
    intro sc member
    rw [← terminal] at member
    exact avoids sc (List.mem_filter.mp member).1
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success ⊢
  obtain ⟨target, merged, merging, continued⟩ := (success_bind _ _ _ _ _).mp success
  have mergingMoved := mergeTerminal_neutral graph held (fuel + 1) first rest before merged target safe.1.total root selectedAvoid merging
  have separate := (mergeTerminal_protected graph (fuel + 1) first rest held before merged target safe.1.total root selectedAvoid merging).2.2.1
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have restrictionMoved := mergeNode_neutral graph held (fuel + 1) target node _ merged restricted separate restriction
  obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole target) fragment restricted after).mp final
  subst fragment
  subst after
  exact (success_bind _ _ _ _ _).mpr ⟨target, neutralize held merged, mergingMoved,
    (success_bind _ _ _ _ _).mpr ⟨(), neutralize held restricted, restrictionMoved,
      (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩

/-- Repeated fresh allocation commutes with neutralization of an older slot. -/
theorem neutralize_suspended (held count : Nat) (before : State Symbol Guard) (inside : held < before.values.length) :
    neutralize held (suspendedState count before) = suspendedState count (neutralize held before) := by
  induction count generalizing before with
  | zero => rfl
  | succ count ih =>
      rw [suspendedState, ih (allocated none before) (by simpa [allocated] using Nat.lt_succ_of_lt inside),
        neutralize_allocated held none before inside]
      rfl

/-- Retaining a residual is independent of every stored payload. -/
theorem recordResidual_neutral (held : Nat) (residual : Option Guard) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (success : Success (recordResidual residual fragment) before () after) :
    Success (recordResidual residual fragment) (neutralize held before) () (neutralize held after) := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact (success_pure () () _ _).mpr ⟨rfl, rfl⟩
  | some guard =>
      obtain rfl := (modify_success _ before after).mp success
      exact (modify_success _ _ _).mpr rfl

/-- Actual node and edge traversal is independent of a separate protected root payload. -/
theorem enumeration_neutral (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node held (before after : State Symbol Guard) fragment, Safe before →
      held < before.counter → IsRoot before.representatives held →
      (∀ sc ∈ scs, sc.var < before.counter) → Avoids before.representatives held scs →
      Success (enumerateNode graph fuel scs node) before fragment after →
      Success (enumerateNode graph fuel scs node) (neutralize held before) fragment (neutralize held after)) ∧
    (∀ scs edge held (before after : State Symbol Guard) fragment, Safe before →
      held < before.counter → IsRoot before.representatives held →
      (∀ sc ∈ scs, sc.var < before.counter) → Avoids before.representatives held scs →
      Success (enumerateEdge graph fuel scs edge) before fragment after →
      Success (enumerateEdge graph fuel scs edge) (neutralize held before) fragment (neutralize held after)) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node held before after fragment _ _ _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge held before after fragment _ _ _ _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node held before after fragment safe inside root bounded avoids success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                exact enumerateNode_terminal_neutral graph held fuel node scs first rest before after fragment safe root avoids
                  (by simp [view]) terminal success
            | nil =>
                simp only [enumerateNode, view, terminal] at success ⊢
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨member, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact (success_bind _ _ _ _ _).mpr ⟨edge, neutralize held before,
                     (choose_success _ _ _ edge).mpr ⟨member, rfl⟩,
                     ih.2 scs edge held before after fragment safe inside root bounded avoids continued⟩)
                | (obtain ⟨uv, middle, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have insideValues : held < before.values.length := by rw [← safe.1.aligned]; exact inside
                   have moved := allocate_neutral held (some node) before middle uv insideValues allocation
                   obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole uv) fragment middle after).mp final
                   subst fragment
                   subst after
                   exact (success_bind _ _ _ _ _).mpr ⟨uv, neutralize held middle, moved,
                     (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩)
      · intro scs edge held before after fragment safe inside root bounded avoids success
        rw [edge_action graph fuel scs edge] at success ⊢
        obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp success
        cases ignored
        obtain ⟨arity, same⟩ := (require_success _ before checked).mp required
        subst checked
        obtain ⟨added, suspended, suspension, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have suspensionExact : added = suspendedVars before.counter edge.equalities ∧
            suspended = suspendedState edge.equalities.length before := by
          simpa [Success, suspendMany_exact, ExceptT.run] using suspension
        obtain ⟨addedSame, suspendedSame⟩ := suspensionExact
        subst added
        subst suspended
        let start := suspendedState edge.equalities.length before
        let inputs := scs ++ suspendedVars before.counter edge.equalities
        have insideValues : held < before.values.length := by rw [← safe.1.aligned]; exact inside
        have suspensionMoved : Success (edge.equalities.mapM suspend) (neutralize held before)
            (suspendedVars before.counter edge.equalities) (neutralize held start) := by
          rw [show neutralize held start = suspendedState edge.equalities.length (neutralize held before) from
            neutralize_suspended held edge.equalities.length before insideValues]
          simp [Success, suspendMany_exact, ExceptT.run, neutralize]
        have startSafe : Safe start := suspension_safe edge.equalities.length before safe
        have startFrame : Protected held before start := suspension_protected held edge.equalities.length before safe inside root
        have startGrowth : before.counter ≤ start.counter := by simp [start, suspended_counter]
        have startInside : held < start.counter := Nat.lt_of_lt_of_le inside startGrowth
        have inputBound : ∀ sc ∈ inputs, sc.var < start.counter := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact Nat.lt_of_lt_of_le (bounded sc old) startGrowth
          · simpa [start, suspended_counter] using suspended_bounded before.counter edge.equalities sc fresh
        have inputAvoid : Avoids start.representatives held inputs := by
          apply startFrame.avoids
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact avoids sc old
          · exact fresh_avoids before safe.1 held inside edge.equalities sc fresh
        obtain ⟨children, expanded, traversed, continued⟩ := (success_bind _ _ _ _ _).mp continued
        let invariant := fun state : State Symbol Guard =>
          Safe state ∧ start.counter ≤ state.counter ∧ Protected held start state
        have childStep : ∀ entry ∈ edge.children.zipIdx, ∀ previous child next, invariant previous →
            Success (enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) previous child next →
            invariant next ∧ Success (enumerateNode graph fuel (descendScs entry.2 inputs) entry.1)
              (neutralize held previous) child (neutralize held next) := by
          intro entry _ previous child next valid childSuccess
          have childBound : ∀ sc ∈ descendScs entry.2 inputs, sc.var < previous.counter := by
            apply descend_bounded
            intro sc member
            exact Nat.lt_of_lt_of_le (inputBound sc member) valid.2.1
          have childAvoid := descend_avoids previous.representatives held entry.2 inputs (valid.2.2.avoids inputs inputAvoid)
          have childInside := Nat.lt_of_lt_of_le startInside valid.2.1
          obtain ⟨nextSafe, growth, _⟩ := (enumeration_safety graph fuel).1 _ entry.1 previous next child valid.1 childBound childSuccess
          have frame := (enumeration_protected graph fuel).1 _ entry.1 held previous next child valid.1 childInside
            valid.2.2.root childBound childAvoid childSuccess
          exact ⟨⟨nextSafe, Nat.le_trans valid.2.1 growth, valid.2.2.trans frame⟩,
            ih.1 _ entry.1 held previous next child valid.1 childInside valid.2.2.root childBound childAvoid childSuccess⟩
        have traversalMoved := mapM_transport
          (fun entry => enumerateNode graph fuel (descendScs entry.2 inputs) entry.1) (neutralize held) invariant
          edge.children.zipIdx childStep start expanded children ⟨startSafe, Nat.le_refl _, .refl held start startFrame.root⟩ traversed
        obtain ⟨ignored, guarded, residual, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have residualMoved := recordResidual_neutral held edge.residual (.node edge.symbol children) expanded guarded residual
        obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst fragment
        subst after
        exact (success_bind _ _ _ _ _).mpr ⟨(), neutralize held before,
          (require_success _ _ _).mpr ⟨arity, rfl⟩,
          (success_bind _ _ _ _ _).mpr ⟨suspendedVars before.counter edge.equalities, neutralize held start, suspensionMoved,
            (success_bind _ _ _ _ _).mpr ⟨children, neutralize held expanded, traversalMoved,
              (success_bind _ _ _ _ _).mpr ⟨(), neutralize held guarded, residualMoved,
                (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩⟩⟩⟩

/-- Removing one payload restriction preserves every complete assignment. -/
theorem neutralize_satisfies (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (held : Nat) (state : State Symbol Guard)
    (satisfies : Satisfies language meaning assignment state) :
    Satisfies language meaning assignment (neutralize held state) := by
  refine ⟨⟨satisfies.1.1, ?_⟩, satisfies.2⟩
  intro uv
  by_cases same : uv = held
  · subst uv
    by_cases inside : held < state.values.length
    · simp [neutralize, heap, inside, slot, slotSatisfies, permits]
    · simp [neutralize, heap, inside, slot, slotSatisfies]
  · simpa [heap, neutralize_read held uv state same] using satisfies.1.2 uv

/-- Reestablishing the selected payload completes a neutral state's assignment. -/
theorem neutralize_restore (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (held : Nat) (state : State Symbol Guard)
    (satisfies : Satisfies language meaning assignment (neutralize held state))
    (selected : slotSatisfies assignment held (heap language state.values held)) :
    Satisfies language meaning assignment state := by
  refine ⟨⟨satisfies.1.1, ?_⟩, satisfies.2⟩
  intro uv
  by_cases same : uv = held
  · simpa [same] using selected
  · have other := satisfies.1.2 uv
    simpa [heap, neutralize_read held uv state same] using other

/-- Neutralizing after a selected-slot write removes exactly that write. -/
theorem neutralize_overwrite (held : Nat) (value : UVarValue Symbol) (state : State Symbol Guard) :
    neutralize held {state with values := state.values.set held value} = neutralize held state := by
  simp [neutralize]

/-- A successful value read preserves every complete assignment. -/
theorem getValue_assignment (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (total : UnionFind.Total before.representatives) (success : Success (getValue fuel uv) before value after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before := by
  obtain ⟨found, lookup, _, rfl⟩ := (getValue_success fuel uv before after value).mp success
  exact representative_semantics language meaning assignment fuel uv before found total lookup

/-- Complete graph views do not change the selected node at a recursive expansion boundary. -/
theorem complete_expansion (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (node : Nat) :
    (match graph.node node with | .recursive body => body | _ => node) = node := by
  cases view : graph.node node with
  | empty | alternatives _ | unresolved _ => rfl
  | recursive body => exact (complete.1 node body view).elim

/-- The actual final root write preserves prior assignments without assuming its pending restriction. -/
theorem enumerateOut_backward (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (assignment : Nat → Term Symbol) (fuel uv : Nat) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (ready : Ready uv before)
    (valid : ∀ node scs, before.values[uv]? = some (.unenumerated (some node) scs) → ValidSuspended scs)
    (success : Success (enumerateOut graph fuel uv) before fragment after)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment after) :
    Satisfies (Accepted graph meaning) meaning assignment before ∧ fill assignment fragment = assignment uv := by
  unfold enumerateOut at success
  obtain ⟨value, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readSafe, readCounter, readFrame, stored⟩ := getValue_root (fuel + 1) uv before readState value ready.safe ready.inside ready.root reading
  cases value with
  | eliminated | enumerated _ => exact (reject_unsuccessful readState after fragment continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful readState after fragment continued).elim
      | some node =>
          obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨selectedSame, resolvedSafe, resolvedCounter, resolvedFrame⟩ := representative_root (fuel + 1) uv selected
            readState resolved readSafe (by simpa [readCounter] using ready.inside) readFrame.root resolution
          subst selected
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
          let start := {resolved with expansionAncestry := ancestry}
          have expansion : Success (enumerateNode graph fuel scs node) start produced expanded := by
            cases view : graph.node node with
            | recursive body => exact (complete.1 node body view).elim
            | empty | alternatives _ | unresolved _ => simpa only [start, ancestry, view] using expansion
          have startSafe : Safe start := ancestry_safe resolved ancestry resolvedSafe
          have startInside : uv < start.counter := by simpa [start, resolvedCounter, readCounter] using ready.inside
          have movedExpansion := (enumeration_neutral graph fuel).1 scs node uv start expanded produced startSafe
            startInside resolvedFrame.root bounded separate expansion
          obtain ⟨expandedSafe, growth, _⟩ := (enumeration_safety graph fuel).1 scs node start expanded produced startSafe bounded expansion
          obtain ⟨ignored, cleared, bookkeeping, continued⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain rfl := (modify_success _ expanded cleared).mp bookkeeping
          obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          have writtenSame := (modify_success _ _ written).mp writing
          obtain ⟨fragmentSame, afterSame⟩ := (success_pure produced fragment written after).mp final
          subst fragment
          subst after
          have expandedInside : uv < expanded.counter := Nat.lt_of_lt_of_le startInside growth
          have valueBound : uv < expanded.values.length := by rw [← expandedSafe.1.aligned]; exact expandedInside
          have equation : fill assignment produced = assignment uv := by
            have slotHolds := satisfies.1.2 uv
            simpa [writtenSame, heap, valueBound, slot, slotSatisfies] using slotHolds
          have neutralExpanded : Satisfies (Accepted graph meaning) meaning assignment (neutralize uv expanded) := by
            have neutralWritten := neutralize_satisfies (Accepted graph meaning) meaning assignment uv written satisfies
            rw [writtenSame, neutralize_overwrite] at neutralWritten
            exact neutralWritten
          obtain ⟨neutralStart, accepted, inherited⟩ := (enumeration_backward graph meaning complete correct assignment fuel).1
            scs node (neutralize uv start) (neutralize uv expanded) produced (neutralize_safe uv start startSafe resolvedFrame.root)
            bounded (valid node scs oldStored) movedExpansion neutralExpanded
          have selectedHolds : slotSatisfies assignment uv (heap (Accepted graph meaning) start.values uv) := by
            have selectedStored : start.values[uv]? = some (.unenumerated (some node) scs) := by
              exact resolvedFrame.value ▸ stored
            simp only [heap, selectedStored, Option.getD_some, slot, slotSatisfies, Option.map_some, permits,
              List.mem_map, forall_exists_index, and_imp]
            refine ⟨by simpa [equation] using accepted, ?_⟩
            intro obligation sc member same
            subst obligation
            simpa [equation] using inherited sc member
          have startSatisfies := neutralize_restore (Accepted graph meaning) meaning assignment uv start neutralStart selectedHolds
          have resolvedSatisfies : Satisfies (Accepted graph meaning) meaning assignment resolved := startSatisfies
          have readSatisfies := (representative_assignment (Accepted graph meaning) meaning assignment (fuel + 1) uv uv
            readState resolved readSafe.1.total resolution).2.mp resolvedSatisfies
          exact ⟨(getValue_assignment (Accepted graph meaning) meaning assignment (fuel + 1) uv before readState _ ready.safe.1.total reading).mp readSatisfies,
            equation⟩

end MicroCFTA.EnumerationFrame
