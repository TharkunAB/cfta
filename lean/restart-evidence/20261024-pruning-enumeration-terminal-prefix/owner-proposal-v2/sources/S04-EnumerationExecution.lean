import MicroCFTA.EnumerationAssignment

/-!
# Existence and bounds for concrete enumeration actions

Successful executions remain available when their bound increases.
Total forests give successful scheduler scans at a sufficient finite bound.
-/

namespace MicroCFTA.EnumerationExecution
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment

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

/-- One action retains every successful state transition of another action. -/
def Retains (first second : EnumerateM Symbol Guard α) : Prop :=
  ∀ before value after, Success first before value after → Success second before value after

/-- Sequential actions compose successful-branch inclusion. -/
theorem retains_bind (first second : EnumerateM Symbol Guard α)
    (left right : α → EnumerateM Symbol Guard β) (initial : Retains first second)
    (continued : ∀ value, Retains (left value) (right value)) :
    Retains (first >>= left) (second >>= right) := by
  intro before result after success
  obtain ⟨value, middle, step, rest⟩ := (success_bind _ _ _ _ _).mp success
  exact (success_bind _ _ _ _ _).mpr ⟨value, middle, initial _ _ _ step, continued value _ _ _ rest⟩

/-- An unchanged continuation retains successful branches. -/
theorem retains_refl (action : EnumerateM Symbol Guard α) : Retains action action := fun _ _ _ success => success

/-- List traversal retains each successful ordered result. -/
theorem retains_mapM (left right : α → EnumerateM Symbol Guard β)
    (step : ∀ input, Retains (left input) (right input)) (inputs : List α) :
    Retains (inputs.mapM left) (inputs.mapM right) := by
  induction inputs with
  | nil => exact retains_refl _
  | cons input rest ih =>
      simp only [List.mapM_cons]
      apply retains_bind _ _ _ _ (step input)
      intro output
      exact retains_bind _ _ _ _ ih (fun _ => retains_refl _)

/-- A fold retains its successful accumulator and state. -/
theorem retains_foldlM (left right : α → β → EnumerateM Symbol Guard α)
    (step : ∀ accumulator input, Retains (left accumulator input) (right accumulator input))
    (inputs : List β) (accumulator : α) :
    Retains (inputs.foldlM left accumulator) (inputs.foldlM right accumulator) := by
  induction inputs generalizing accumulator with
  | nil => exact retains_refl _
  | cons input rest ih =>
      simp only [List.foldlM_cons]
      exact retains_bind _ _ _ _ (step accumulator input) ih

/-- A discarded-result traversal retains every successful state. -/
theorem retains_forM (left right : α → EnumerateM Symbol Guard PUnit)
    (step : ∀ input, Retains (left input) (right input)) (inputs : List α) :
    Retains (inputs.forM left) (inputs.forM right) := by
  induction inputs with
  | nil => exact retains_refl _
  | cons input rest ih =>
      change Retains (left input >>= fun _ => rest.forM left) (right input >>= fun _ => rest.forM right)
      exact retains_bind _ _ _ _ (step input) (fun _ => ih)

/-- Increasing both lookup bounds preserves the exact union forest. -/
theorem union_moreFuel (leftFuel rightFuel leftExtra rightExtra : Nat) (forest : UnionFind.Forest)
    (left right : Nat) (after : UnionFind.Forest)
    (success : UnionFind.union leftFuel rightFuel forest left right = some after) :
    UnionFind.union (leftFuel + leftExtra) (rightFuel + rightExtra) forest left right = some after := by
  cases first : UnionFind.findRoot leftFuel forest left with
  | none => simp [UnionFind.union, first] at success
  | some result =>
      have firstMore := UnionFind.findRoot_moreFuel leftFuel leftExtra forest left result first
      cases second : UnionFind.findRoot rightFuel result.forest right with
      | none => simp [UnionFind.union, first, second] at success
      | some other =>
          have secondMore := UnionFind.findRoot_moreFuel rightFuel rightExtra result.forest right other second
          simpa [UnionFind.union, first, second, firstMore, secondMore] using success

/-- Representative lookup retains its exact compression state at larger bounds. -/
theorem representative_moreFuel (fuel extra uv : Nat) :
    Retains (representative (Symbol := Symbol) (Guard := Guard) fuel uv) (representative (fuel + extra) uv) := by
  intro before root after success
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact (representative_success (fuel + extra) uv before _ _).mpr
    ⟨found, UnionFind.findRoot_moreFuel fuel extra before.representatives uv found lookup, rfl, rfl⟩

/-- Reading a representative value retains its successful slot result. -/
theorem getValue_moreFuel (fuel extra uv : Nat) :
    Retains (getValue (Symbol := Symbol) (Guard := Guard) fuel uv) (getValue (fuel + extra) uv) := by
  unfold getValue
  exact retains_bind _ _ _ _ (representative_moreFuel fuel extra uv) (fun _ => retains_refl _)

/-- An equality-variable union retains its exact successful state. -/
theorem unionVariables_moreFuel (fuel extra left right : Nat) :
    Retains (unionVariables (Symbol := Symbol) (Guard := Guard) fuel left right)
      (unionVariables (fuel + extra) left right) := by
  intro before ignored after success
  cases ignored
  obtain ⟨forest, lookup, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact (unionVariables_success (fuel + extra) left right before _).mpr
    ⟨forest, union_moreFuel fuel fuel extra extra before.representatives left right forest lookup, rfl⟩

/-- Pending-node merging uses the same slot after additional lookup fuel. -/
theorem mergeNode_moreFuel (graph : Graph Symbol Guard) (fuel extra uv node : Nat) (scs : List Suspended) :
    Retains (mergeNode graph fuel uv node scs) (mergeNode graph (fuel + extra) uv node scs) := by
  unfold mergeNode
  exact retains_bind _ _ _ _ (representative_moreFuel fuel extra uv) (fun _ => retains_refl _)

/-- The complete terminal merge retains all successful choices with more fuel. -/
theorem mergeTerminal_moreFuel (graph : Graph Symbol Guard) (fuel extra : Nat) (first : Suspended) (rest : List Suspended) :
    Retains (mergeTerminal graph fuel first rest) (mergeTerminal graph (fuel + extra) first rest) := by
  unfold mergeTerminal
  apply retains_bind _ _ _ _ (retains_mapM _ _ (fun (sc : Suspended) => representative_moreFuel fuel extra sc.var) _)
  intro roots
  apply retains_bind _ _ _ _ (retains_forM _ _ (fun (sc : Suspended) => unionVariables_moreFuel fuel extra first.var sc.var) _)
  intro ignored
  apply retains_bind _ _ _ _ (representative_moreFuel fuel extra first.var)
  intro root
  exact retains_refl _

/-- Actual mutual node and edge traversal retains its exact branch at larger bounds. -/
theorem enumeration_moreFuel (graph : Graph Symbol Guard) (fuel extra : Nat) :
    (∀ scs node, Retains (enumerateNode graph fuel scs node) (enumerateNode graph (fuel + extra) scs node)) ∧
    (∀ scs edge, Retains (enumerateEdge graph fuel scs edge) (enumerateEdge graph (fuel + extra) scs edge)) := by
  induction fuel with
  | zero =>
      constructor <;> intros _ _ before value after success
      all_goals simp [enumerateNode, enumerateEdge, Success, EnumerationState.failure, ExceptT.run] at success
  | succ fuel ih =>
      constructor
      · intro scs node
        rw [Nat.succ_add]
        cases view : graph.node node with
        | empty => simp only [enumerateNode, view]; exact retains_refl _
        | alternatives edges =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | nil =>
                simp only [enumerateNode, view, terminal]
                exact retains_bind _ _ _ _ (retains_refl _) (fun edge => ih.2 scs edge)
            | cons first rest =>
                rw [terminal_branch graph fuel node scs first rest (by simp [view]) terminal,
                  terminal_branch graph (fuel + extra) node scs first rest (by simp [view]) terminal]
                apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using mergeTerminal_moreFuel graph (fuel + 1) extra first rest)
                intro root
                apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using mergeNode_moreFuel graph (fuel + 1) extra root node (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie))
                exact fun _ => retains_refl _
        | recursive body =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | nil => simp only [enumerateNode, view, terminal]; exact retains_refl _
            | cons first rest =>
                rw [terminal_branch graph fuel node scs first rest (by simp [view]) terminal,
                  terminal_branch graph (fuel + extra) node scs first rest (by simp [view]) terminal]
                apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using mergeTerminal_moreFuel graph (fuel + 1) extra first rest)
                intro root
                apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using mergeNode_moreFuel graph (fuel + 1) extra root node (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie))
                exact fun _ => retains_refl _
        | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | nil => simp only [enumerateNode, view, terminal]; exact retains_refl _
            | cons first rest =>
                rw [terminal_branch graph fuel node scs first rest (by simp [view]) terminal,
                  terminal_branch graph (fuel + extra) node scs first rest (by simp [view]) terminal]
                apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using mergeTerminal_moreFuel graph (fuel + 1) extra first rest)
                intro root
                apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using mergeNode_moreFuel graph (fuel + 1) extra root node (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie))
                exact fun _ => retains_refl _
      · intro scs edge
        rw [Nat.succ_add]
        simp only [enumerateEdge]
        apply retains_bind _ _ _ _ (retains_refl _)
        intro ignored
        apply retains_bind _ _ _ _ (retains_refl _)
        intro added
        apply retains_bind _ _ _ _ (retains_mapM _ _ (fun (pair : Nat × Nat) => ih.1 (descendScs pair.2 (scs ++ added)) pair.1) _)
        exact fun _ => retains_refl _

/-- Each blocked-reference lookup retains its successful scan update. -/
theorem resolve_moreFuel (fuel extra : Nat) (blocked : List Nat) (sc : Suspended) :
    Retains (resolve (Symbol := Symbol) (Guard := Guard) fuel blocked sc) (resolve (fuel + extra) blocked sc) := by
  unfold resolve
  exact retains_bind _ _ _ _ (representative_moreFuel fuel extra sc.var) (fun _ => retains_refl _)

/-- Each actual value-slot scan retains its result at larger bounds. -/
theorem collect_moreFuel (graph : Graph Symbol Guard) (fuel extra : Nat)
    (accumulator : List Nat × List Nat) (entry : UVarValue Symbol × Nat) :
    Retains (collect graph fuel accumulator entry) (collect graph (fuel + extra) accumulator entry) := by
  obtain ⟨candidates, blocked⟩ := accumulator
  obtain ⟨value, index⟩ := entry
  cases value with
  | eliminated | enumerated _ => exact retains_refl _
  | unenumerated node scs =>
      unfold collect
      exact retains_bind _ _ _ _ (retains_foldlM _ _ (resolve_moreFuel fuel extra) scs blocked) (fun _ => retains_refl _)

/-- The actual scheduler retains the same offered variables and compressed state. -/
theorem findExpandable_moreFuel (graph : Graph Symbol Guard) (fuel extra : Nat) :
    Retains (findExpandable graph fuel) (findExpandable graph (fuel + extra)) := by
  change Retains (get >>= fun state => state.values.zipIdx.foldlM (collect graph fuel) ([], []) >>= finishScan)
    (get >>= fun state => state.values.zipIdx.foldlM (collect graph (fuel + extra)) ([], []) >>= finishScan)
  apply retains_bind _ _ _ _ (retains_refl _)
  intro state
  exact retains_bind _ _ _ _ (retains_foldlM _ _ (collect_moreFuel graph fuel extra) _ _) (fun _ => retains_refl _)

/-- Expanding a selected root retains the same fragment and final root write. -/
theorem enumerateOut_moreFuel (graph : Graph Symbol Guard) (fuel extra uv : Nat) :
    Retains (enumerateOut graph fuel uv) (enumerateOut graph (fuel + extra) uv) := by
  unfold enumerateOut
  apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using getValue_moreFuel (fuel + 1) extra uv)
  intro value
  cases value with
  | eliminated | enumerated _ => exact retains_refl _
  | unenumerated node scs =>
      cases node with
      | none => exact retains_refl _
      | some node =>
          apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using representative_moreFuel (fuel + 1) extra uv)
          intro root
          apply retains_bind _ _ _ _ (retains_refl _)
          intro state
          apply retains_bind _ _ _ _ (retains_refl _)
          intro ignored
          exact retains_bind _ _ _ _ ((enumeration_moreFuel graph fuel extra).1 scs _) (fun _ => retains_refl _)

/-- Repeated-recursion bookkeeping retains its successful result at larger bounds. -/
theorem checkRepeated_moreFuel (graph : Graph Symbol Guard) (fuel extra uv node : Nat) (scs : List Suspended) :
    Retains (checkRepeated graph fuel uv node scs) (checkRepeated graph (fuel + extra) uv node scs) := by
  unfold checkRepeated
  cases graph.node node with
  | empty | alternatives _ | unresolved _ => exact retains_refl _
  | recursive body => exact retains_bind _ _ _ _ (representative_moreFuel fuel extra uv) (fun _ => retains_refl _)

/-- The full source caller retains each successful branch at every larger bound. -/
theorem enumerateFully_moreFuel (graph : Graph Symbol Guard) (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) (fuel extra : Nat) (oracleState : OracleState) :
    Retains (enumerateFully graph order oracle fuel oracleState) (enumerateFully graph order oracle (fuel + extra) oracleState) := by
  induction fuel generalizing oracleState with
  | zero =>
      intro before value after success
      exact (success_failure .fuelExhausted before after value success).elim
  | succ fuel ih =>
      rw [Nat.succ_add, fully_action, fully_action]
      apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using findExpandable_moreFuel graph (fuel + 1) extra)
      intro available
      cases pickNext (order oracleState) available with
      | done | stuck => exact retains_refl _
      | expand uv =>
          apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using getValue_moreFuel (fuel + 1) extra uv)
          intro value
          cases value with
          | eliminated | enumerated _ => exact retains_refl _
          | unenumerated node scs =>
              cases node with
              | none => exact retains_refl _
              | some node =>
                  apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using checkRepeated_moreFuel graph (fuel + 1) extra uv node scs)
                  intro repeated
                  cases repeated with
                  | true => exact ih oracleState
                  | false =>
                      apply retains_bind _ _ _ _ (retains_refl _)
                      intro beforeResult
                      apply retains_bind _ _ _ _ (retains_refl _)
                      intro ignored
                      apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using enumerateOut_moreFuel graph (fuel + 1) extra uv)
                      intro fragment
                      apply retains_bind _ _ _ _ (retains_refl _)
                      intro afterResult
                      exact retains_bind _ _ _ _ (retains_refl _) (fun _ => ih afterResult.2)

/-- Concrete fragment rendering retains its exact term and compression state. -/
theorem expandFragment_moreFuel (graph : Graph Symbol Guard) (marker : Symbol) (fuel extra : Nat)
    (fragment : Fragment Symbol) :
    Retains (expandFragment graph marker fuel fragment) (expandFragment graph marker (fuel + extra) fragment) := by
  induction fuel generalizing fragment with
  | zero =>
      intro before value after success
      exact (success_failure .fuelExhausted before after value success).elim
  | succ fuel ih =>
      rw [Nat.succ_add]
      cases fragment with
      | node symbol children =>
          simp only [expandFragment]
          exact retains_bind _ _ _ _ (retains_mapM _ _ ih children) (fun _ => retains_refl _)
      | hole uv =>
          simp only [expandFragment]
          apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using getValue_moreFuel (fuel + 1) extra uv)
          intro value
          cases value with
          | eliminated => exact retains_refl _
          | enumerated fragment => exact ih fragment
          | unenumerated node scs => cases node <;> exact retains_refl _

/-- Root rendering retains its exact term and compression state. -/
theorem expandUVar_moreFuel (graph : Graph Symbol Guard) (marker : Symbol) (fuel extra uv : Nat) :
    Retains (expandUVar graph marker fuel uv) (expandUVar graph marker (fuel + extra) uv) := by
  unfold expandUVar
  apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using getValue_moreFuel (fuel + 1) extra uv)
  intro value
  cases value with
  | eliminated => exact retains_refl _
  | enumerated fragment => exact expandFragment_moreFuel graph marker fuel extra fragment
  | unenumerated node scs => cases node <;> exact retains_refl _

/-- The public initialized run retains its returned term, residuals, and state at every larger bound. -/
theorem runs_moreFuel (graph : Graph Symbol Guard) (marker : Symbol) (fuel extra root : Nat)
    (term : Term Symbol) (pending : List (Guard × Term Symbol)) (after : State Symbol Guard)
    (success : .ok ((term, pending), after) ∈ runs graph marker fuel root) :
    .ok ((term, pending), after) ∈ runs graph marker (fuel + extra) root := by
  have retained : Retains (do
      enumerateFully graph (fun _ _ => none) noPruning fuel ()
      let term ← expandUVar graph marker fuel 0
      let pending ← (← get).obligations.mapM fun (guard, fragment) => do
        pure (guard, ← expandFragment graph marker fuel fragment)
      pure (term, pending)) (do
      enumerateFully graph (fun _ _ => none) noPruning (fuel + extra) ()
      let term ← expandUVar graph marker (fuel + extra) 0
      let pending ← (← get).obligations.mapM fun (guard, fragment) => do
        pure (guard, ← expandFragment graph marker (fuel + extra) fragment)
      pure (term, pending)) := by
    apply retains_bind _ _ _ _ (enumerateFully_moreFuel graph _ noPruning fuel extra ())
    intro ignored
    apply retains_bind _ _ _ _ (expandUVar_moreFuel graph marker fuel extra 0)
    intro term
    apply retains_bind _ _ _ _ (retains_refl _)
    intro state
    apply retains_bind _ _ _ _ (retains_mapM _ _ (fun (obligation : Guard × Fragment Symbol) =>
      retains_bind _ _ _ _ (expandFragment_moreFuel graph marker fuel extra obligation.2) (fun _ => retains_refl _)) state.obligations)
    exact fun _ => retains_refl _
  exact retained (initial root) (term, pending) after success

/-- Sequential fold steps with finite bounds have one common sufficient bound. -/
theorem foldlM_terminates (action : Nat → α → β → EnumerateM Symbol Guard α)
    (invariant : State Symbol Guard → Prop)
    (more : ∀ fuel extra accumulator input, Retains (action fuel accumulator input) (action (fuel + extra) accumulator input))
    (step : ∀ accumulator input before, invariant before →
      ∃ fuel value after, Success (action fuel accumulator input) before value after ∧ invariant after)
    (inputs : List β) (accumulator : α) (before : State Symbol Guard) (valid : invariant before) :
    ∃ fuel value after, Success (inputs.foldlM (action fuel) accumulator) before value after ∧ invariant after := by
  induction inputs generalizing accumulator before with
  | nil => exact ⟨0, accumulator, before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, valid⟩
  | cons input rest ih =>
      obtain ⟨firstFuel, value, middle, first, middleValid⟩ := step accumulator input before valid
      obtain ⟨restFuel, result, after, continued, afterValid⟩ := ih value middle middleValid
      refine ⟨firstFuel + restFuel, result, after, ?_, afterValid⟩
      rw [List.foldlM_cons]
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨value, middle, more firstFuel restFuel accumulator input _ _ _ first, ?_⟩
      have extended := retains_foldlM _ _ (more restFuel firstFuel) rest value _ _ _ continued
      simpa [Nat.add_comm] using extended

/-- Ordered child actions with finite bounds have one common sufficient bound. -/
theorem mapM_terminates (action : Nat → α → EnumerateM Symbol Guard β)
    (invariant : State Symbol Guard → Prop)
    (more : ∀ fuel extra input, Retains (action fuel input) (action (fuel + extra) input))
    (step : ∀ input before, invariant before →
      ∃ fuel value after, Success (action fuel input) before value after ∧ invariant after)
    (inputs : List α) (before : State Symbol Guard) (valid : invariant before) :
    ∃ fuel values after, Success (inputs.mapM (action fuel)) before values after ∧ invariant after := by
  induction inputs generalizing before with
  | nil => exact ⟨0, [], before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, valid⟩
  | cons input rest ih =>
      obtain ⟨firstFuel, value, middle, first, middleValid⟩ := step input before valid
      obtain ⟨restFuel, values, after, continued, afterValid⟩ := ih middle middleValid
      refine ⟨firstFuel + restFuel, value :: values, after, ?_, afterValid⟩
      rw [List.mapM_cons]
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨value, middle, more firstFuel restFuel input _ _ _ first, ?_⟩
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨values, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
      have extended := retains_mapM _ _ (more restFuel firstFuel) rest _ _ _ continued
      simpa [Nat.add_comm] using extended

/-- Discarded-result actions with finite bounds have one common sufficient bound. -/
theorem forM_terminates (action : Nat → α → EnumerateM Symbol Guard PUnit)
    (invariant : State Symbol Guard → Prop)
    (more : ∀ fuel extra input, Retains (action fuel input) (action (fuel + extra) input))
    (step : ∀ input before, invariant before →
      ∃ fuel after, Success (action fuel input) before () after ∧ invariant after)
    (inputs : List α) (before : State Symbol Guard) (valid : invariant before) :
    ∃ fuel after, Success (inputs.forM (action fuel)) before () after ∧ invariant after := by
  induction inputs generalizing before with
  | nil => exact ⟨0, before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, valid⟩
  | cons input rest ih =>
      obtain ⟨firstFuel, middle, first, middleValid⟩ := step input before valid
      obtain ⟨restFuel, after, continued, afterValid⟩ := ih middle middleValid
      refine ⟨firstFuel + restFuel, after, ?_, afterValid⟩
      change Success (action (firstFuel + restFuel) input >>= fun _ => rest.forM (action (firstFuel + restFuel))) before () after
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨(), middle, more firstFuel restFuel input _ _ _ first, ?_⟩
      have extended := retains_forM _ _ (more restFuel firstFuel) rest _ _ _ continued
      simpa [Nat.add_comm] using extended

/-- A total forest gives a successful actual representative action. -/
theorem representative_terminates (before : State Symbol Guard) (total : UnionFind.Total before.representatives) (uv : Nat) :
    ∃ fuel root after, Success (representative fuel uv) before root after ∧ UnionFind.Total after.representatives := by
  obtain ⟨root, size, path⟩ := total uv
  obtain ⟨fuel, found, lookup⟩ := UnionFind.findRoot_terminates path
  exact ⟨fuel, found.representative, {before with representatives := found.forest},
    (representative_success _ _ _ _ _).mpr ⟨found, lookup, rfl, rfl⟩, UnionFind.findRoot_total total lookup⟩

/-- Actual union has one sufficient bound for both representative lookups. -/
theorem unionVariables_terminates (before : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (left right : Nat) :
    ∃ fuel after, Success (unionVariables fuel left right) before () after ∧ UnionFind.Total after.representatives := by
  obtain ⟨leftFuel, rightFuel, forest, lookup⟩ := UnionFind.union_terminates total left right
  have extended : UnionFind.union (leftFuel + rightFuel) (leftFuel + rightFuel) before.representatives left right = some forest := by
    simpa [Nat.add_comm] using union_moreFuel leftFuel rightFuel rightFuel leftFuel before.representatives left right forest lookup
  exact ⟨leftFuel + rightFuel, {before with representatives := forest},
    (unionVariables_success _ _ _ _ _).mpr ⟨forest, extended, rfl⟩, (UnionFind.union_correct total extended).1⟩

/-- Resolving one blocked reference always terminates in a total forest. -/
theorem resolve_terminates (before : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (blocked : List Nat) (sc : Suspended) :
    ∃ fuel result after, Success (resolve fuel blocked sc) before result after ∧ UnionFind.Total after.representatives := by
  obtain ⟨fuel, root, after, success, valid⟩ := representative_terminates before total sc.var
  refine ⟨fuel, root :: blocked, after, ?_, valid⟩
  exact (success_bind _ _ _ _ _).mpr ⟨root, after, success, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- Each stored-slot scan has a sufficient finite execution bound. -/
theorem collect_terminates (graph : Graph Symbol Guard) (before : State Symbol Guard)
    (total : UnionFind.Total before.representatives) (accumulator : List Nat × List Nat) (entry : UVarValue Symbol × Nat) :
    ∃ fuel result after, Success (collect graph fuel accumulator entry) before result after ∧ UnionFind.Total after.representatives := by
  obtain ⟨candidates, blocked⟩ := accumulator
  obtain ⟨value, index⟩ := entry
  cases value with
  | eliminated | enumerated _ => exact ⟨0, (candidates, blocked), before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, total⟩
  | unenumerated node scs =>
      obtain ⟨fuel, resolved, after, success, valid⟩ := foldlM_terminates resolve
        (fun state : State Symbol Guard => UnionFind.Total state.representatives) resolve_moreFuel
        (fun blocked sc state valid => resolve_terminates state valid blocked sc) scs blocked before total
      refine ⟨fuel, (if candidate graph (.unenumerated node scs) then candidates ++ [index] else candidates, resolved), after, ?_, valid⟩
      exact (success_bind _ _ _ _ _).mpr ⟨resolved, after, success, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- The actual scheduler scan always has a sufficient finite bound on a total forest. -/
theorem findExpandable_terminates (graph : Graph Symbol Guard) (before : State Symbol Guard)
    (total : UnionFind.Total before.representatives) :
    ∃ fuel result after, Success (findExpandable graph fuel) before result after := by
  obtain ⟨fuel, summary, after, success, _⟩ := foldlM_terminates (collect graph)
    (fun state : State Symbol Guard => UnionFind.Total state.representatives) (collect_moreFuel graph)
    (fun accumulator entry state valid => collect_terminates graph state valid accumulator entry)
    before.values.zipIdx ([], []) before total
  refine ⟨fuel, offered summary.1 summary.2, after, ?_⟩
  change Success (get >>= fun state => state.values.zipIdx.foldlM (collect graph fuel) ([], []) >>= finishScan) _ _ _
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨before, before, (get_success _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact (success_bind _ _ _ _ _).mpr ⟨summary, after, success, (finishScan_success _ _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- A satisfying safe proper state reaches either completion or available work. -/
theorem findExpandable_progress (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : State Symbol Guard) (safe : Safe before) (proper : ProperState before)
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before) :
    ∃ fuel result after, Success (findExpandable graph fuel) before result after ∧ result ≠ some [] := by
  obtain ⟨fuel, result, after, success⟩ := findExpandable_terminates graph before safe.1.total
  refine ⟨fuel, result, after, success, ?_⟩
  intro blocked
  subst result
  exact findExpandable_not_stuck graph (Accepted graph meaning) meaning assignment fuel before after safe proper satisfies success

end MicroCFTA.EnumerationExecution
