import MicroCFTA.EnumerationStateWorkerIndexValidity

set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateFullyIndexValidity

open EnumerationState EnumerationStateReferenceBounds EnumerationStateIndexValidity

variable {Symbol Guard OracleState α β : Type}

local instance : Monad List where
  pure := fun value => [value]
  bind := fun branches next => List.flatMap next branches

private theorem list_lawful : LawfulMonad List := by
  exact LawfulMonad.mk' (m := List)
    (id_map := by intros; simp [Functor.map])
    (bind_pure_comp := by
      intro α β f values
      induction values with
      | nil => rfl
      | cons first rest ih => simp_all [Bind.bind, Functor.map, Pure.pure, List.flatMap])
    (pure_bind := by intros; simp [Bind.bind, Pure.pure])
    (bind_assoc := by intros; simp [Bind.bind, List.flatMap_assoc])

attribute [local instance] list_lawful

private theorem fragment_mono (held : FragmentBelow lower fragment) (larger : lower ≤ upper) :
    FragmentBelow upper fragment := by
  induction held with
  | hole key below => exact .hole key (Nat.lt_of_lt_of_le below larger)
  | node symbol children below ih => exact .node symbol children (fun child member => ih child member)

private theorem suspensions_mono (held : SuspensionsBelow lower scs) (larger : lower ≤ upper) :
    SuspensionsBelow upper scs := by
  intro entry member
  exact Nat.lt_of_lt_of_le (held entry member) larger

private theorem value_mono (held : ValueBelow lower value) (larger : lower ≤ upper) :
    ValueBelow upper value := by
  cases value with
  | unenumerated node scs => exact suspensions_mono held larger
  | enumerated fragment => exact fragment_mono held larger
  | eliminated => trivial

private def Safe (lower : Nat) (post : Nat → α → Prop)
    (action : EnumerateM Symbol Guard α) : Prop :=
  ∀ before value after, Indexed before → lower ≤ before.counter →
    Except.ok (value, after) ∈ ExceptT.run (action before) →
    Indexed after ∧ post after.counter value ∧ before.counter ≤ after.counter

private theorem mem_bind (first : EnumerateM Symbol Guard α)
    (next : α → EnumerateM Symbol Guard β) (before : EnumerationState.State Symbol Guard)
    (value : β) (after : EnumerationState.State Symbol Guard) :
    Except.ok (value, after) ∈ ExceptT.run ((first >>= next) before) ↔
      ∃ result middle, Except.ok (result, middle) ∈ ExceptT.run (first before) ∧
        Except.ok (value, after) ∈ ExceptT.run (next result middle) := by
  dsimp [Bind.bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run]
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨item, member, run⟩
    cases item with
    | error error => simp [ExceptT.bindCont, Pure.pure] at run
    | ok pair => exact ⟨pair.1, pair.2, member, run⟩
  · rintro ⟨result, middle, member, run⟩
    exact ⟨.ok (result, middle), member, run⟩

private theorem safe_raise (held : Safe lower post action) (larger : lower ≤ upper) :
    Safe upper post action := by
  intro before value after state lowerBound run
  exact held before value after state (Nat.le_trans larger lowerBound) run

private theorem pure_safe (held : ∀ upper, lower ≤ upper → post upper value) :
    Safe lower post (pure value : EnumerateM Symbol Guard α) := by
  intro before result after state lowerBound run
  change Except.ok (result, after) ∈ [Except.ok (value, before)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
  exact ⟨state, held _ lowerBound, Nat.le_refl _⟩

private theorem bind_safe (first : Safe lower pre action)
    (next : ∀ value cap, lower ≤ cap → pre cap value → Safe cap post (following value)) :
    Safe lower post (action >>= following) := by
  intro before value after state lowerBound run
  obtain ⟨result, middle, firstRun, nextRun⟩ := (mem_bind _ _ _ _ _).mp run
  obtain ⟨middleState, firstValue, firstMono⟩ := first before result middle state lowerBound firstRun
  obtain ⟨afterState, resultValue, nextMono⟩ :=
    next result middle.counter (Nat.le_trans lowerBound firstMono) firstValue
      middle value after middleState (Nat.le_refl _) nextRun
  exact ⟨afterState, resultValue, Nat.le_trans firstMono nextMono⟩

private theorem failure_safe (error : EnumerationState.Error) :
    Safe lower post (EnumerationState.failure error : EnumerateM Symbol Guard α) := by
  intro before value after state lowerBound run
  change Except.ok (value, after) ∈ [Except.error error] at run
  simp at run

private theorem reject_safe :
    Safe lower post (EnumerationState.reject : EnumerateM Symbol Guard α) := by
  intro before value after state lowerBound run
  change Except.ok (value, after) ∈ [] at run
  simp at run

private theorem require_safe (condition : Bool) :
    Safe lower (fun _ _ => True) (EnumerationState.require condition : EnumerateM Symbol Guard Unit) := by
  cases condition with
  | false => exact reject_safe
  | true => exact pure_safe (fun _ _ => trivial)

private theorem modify_safe (update : EnumerationState.State Symbol Guard → EnumerationState.State Symbol Guard)
    (preserves : ∀ state, Indexed state → lower ≤ state.counter → Indexed (update state))
    (counter : ∀ state, (update state).counter = state.counter) :
    Safe lower (fun _ _ => True) (modify update : EnumerateM Symbol Guard Unit) := by
  intro before value after state lowerBound run
  change Except.ok (value, after) ∈ [Except.ok ((), update before)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  have equal := congrArg Prod.snd paired
  dsimp only at equal
  subst after
  exact ⟨preserves before state lowerBound, trivial, by rw [counter]; omega⟩

private theorem get_bind_safe
    (next : EnumerationState.State Symbol Guard → EnumerateM Symbol Guard α)
    (held : ∀ before value after, Indexed before → lower ≤ before.counter →
      Except.ok (value, after) ∈ ExceptT.run (next before before) →
      Indexed after ∧ post after.counter value ∧ before.counter ≤ after.counter) :
    Safe lower post ((get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) >>= next) := by
  intro before value after state lowerBound run
  obtain ⟨snapshot, middle, got, continued⟩ := (mem_bind _ _ _ _ _).mp run
  change Except.ok (snapshot, middle) ∈ [Except.ok (before, before)] at got
  have paired := Except.ok.inj (List.mem_singleton.mp got)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
  exact held _ value after state lowerBound continued

private theorem representative_safe (fuel key : Nat) (below : key < lower) :
    Safe lower (fun cap result => result < cap)
      (EnumerationState.representative fuel key : EnumerateM Symbol Guard Nat) := by
  intro before value after state lowerBound run
  obtain ⟨preserved, result, counter⟩ :=
    EnumerationStateReferenceBounds.representative_preserves_references fuel key
      (Nat.lt_of_lt_of_le below lowerBound) before value after state run
  exact ⟨by simpa only [Indexed, ← counter] using preserved, by omega, by omega⟩

private theorem set_preserves_all (predicate : α → Prop) (values : List α) (index : Nat)
    (replacement : α) (held : ∀ value ∈ values, predicate value) (fresh : predicate replacement) :
    ∀ value ∈ values.set index replacement, predicate value := by
  induction values generalizing index with
  | nil => simp
  | cons first rest ih => cases index <;> simp_all [List.set] <;> grind

private theorem lookup_is_member (values : List α) (index : Nat) (value : α)
    (lookup : values[index]? = some value) : value ∈ values := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons first rest ih => cases index <;> simp_all <;> grind

private theorem setValue_safe (key : Nat) (value : UVarValue Symbol) (held : ValueBelow lower value) :
    Safe lower (fun _ _ => True) (EnumerationState.setValue key value : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.setValue
  apply modify_safe
  · intro before state lowerBound
    refine ⟨state.counter, ?_, state.supported, state.parents, state.total, ?_, state.obligations⟩
    · simpa using state.shape
    · exact set_preserves_all _ _ _ _ state.values (value_mono held lowerBound)
  · intro state
    rfl

private theorem rawValue_safe (key : Nat) :
    Safe lower (fun cap value => ValueBelow cap value)
      (EnumerationState.rawValue key : EnumerateM Symbol Guard (UVarValue Symbol)) := by
  unfold EnumerationState.rawValue
  apply get_bind_safe
  intro before value after state lowerBound run
  cases looked : before.values[key]? with
  | none =>
      simp only [looked] at run
      exact failure_safe _ before value after state lowerBound run
  | some cell =>
      simp only [looked] at run
      exact pure_safe (lower := before.counter)
        (fun cap increase => value_mono (state.values cell (lookup_is_member _ _ _ looked)) increase)
        before value after state (Nat.le_refl _) run

private theorem getValue_safe (fuel key : Nat) (below : key < lower) :
    Safe lower (fun cap value => ValueBelow cap value)
      (EnumerationState.getValue fuel key : EnumerateM Symbol Guard (UVarValue Symbol)) := by
  unfold EnumerationState.getValue
  apply bind_safe (representative_safe fuel key below)
  intro root cap larger rootBelow
  exact rawValue_safe root

private theorem get_then_safe
    (next : EnumerationState.State Symbol Guard → EnumerateM Symbol Guard α)
    (held : ∀ snapshot, Safe lower post (next snapshot)) :
    Safe lower post ((get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) >>= next) := by
  apply get_bind_safe
  intro before value after state lowerBound run
  exact held before before value after state lowerBound run

private theorem node_safe (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (references : SuspensionsBelow lower scs) :
    Safe lower (fun cap fragment => FragmentBelow cap fragment)
      (EnumerationState.enumerateNode graph fuel scs node) := by
  intro before fragment after state lowerBound run
  exact enumerateNode_preserves_indices graph fuel node scs before fragment after state
    (suspensions_mono references lowerBound) run

/-- This internal law concerns the two actual callback slots.
The native callback implementation must establish it.
Both Bool results are included. -/
structure OraclePreservesIndices (oracle : Oracle Symbol Guard OracleState) : Prop where
  beforeExpansion : ∀ oracleState key node before answer after,
    Indexed before → key < before.counter →
    Except.ok (answer, after) ∈ ExceptT.run (oracle oracleState key (.inr node) before) →
    Indexed after ∧ before.counter ≤ after.counter
  afterExpansion : ∀ oracleState key fragment before answer after,
    Indexed before → key < before.counter → FragmentBelow before.counter fragment →
    Except.ok (answer, after) ∈ ExceptT.run (oracle oracleState key (.inl fragment) before) →
    Indexed after ∧ before.counter ≤ after.counter

private theorem oracle_before_safe (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (oracleState : OracleState) (key node : Nat)
    (below : key < lower) :
    Safe lower (fun _ _ => True) (oracle oracleState key (.inr node)) := by
  intro before answer after indexed lowerBound run
  obtain ⟨preserved, monotone⟩ := law.beforeExpansion oracleState key node before answer after
    indexed (Nat.lt_of_lt_of_le below lowerBound) run
  exact ⟨preserved, trivial, monotone⟩

private theorem oracle_after_safe (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (oracleState : OracleState) (key : Nat)
    (fragment : Fragments.Fragment Symbol) (below : key < lower)
    (references : FragmentBelow lower fragment) :
    Safe lower (fun _ _ => True) (oracle oracleState key (.inl fragment)) := by
  intro before answer after indexed lowerBound run
  obtain ⟨preserved, monotone⟩ := law.afterExpansion oracleState key fragment before answer after
    indexed (Nat.lt_of_lt_of_le below lowerBound) (fragment_mono references lowerBound) run
  exact ⟨preserved, trivial, monotone⟩

private theorem get_snapshot_safe
    (next : EnumerationState.State Symbol Guard → EnumerateM Symbol Guard α)
    (held : ∀ snapshot, Indexed snapshot → Safe snapshot.counter post (next snapshot)) :
    Safe lower post ((get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) >>= next) := by
  apply get_bind_safe
  intro before value after indexed lowerBound run
  exact held before indexed before value after indexed (Nat.le_refl _) run

private theorem foldlM_cons_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (step : β → α → m β) (seed : β) (first : α) (rest : List α) :
    (first :: rest).foldlM step seed =
      (do let next ← step seed first; rest.foldlM step next) := by
  rfl

private theorem foldlM_safe (values : List α) (step : β → α → EnumerateM Symbol Guard β)
    (post : Nat → β → Prop)
    (grows : ∀ lower upper value, lower ≤ upper → post lower value → post upper value)
    (held : ∀ cap, lower ≤ cap → ∀ accumulator, post cap accumulator →
      ∀ value ∈ values, Safe cap post (step accumulator value))
    (seed : β) (seedBelow : post lower seed) :
    Safe lower post (values.foldlM step seed) := by
  induction values generalizing lower seed with
  | nil => exact pure_safe (fun cap larger => grows _ _ _ larger seedBelow)
  | cons first rest ih =>
      rw [foldlM_cons_eq]
      apply bind_safe (held lower (Nat.le_refl _) seed seedBelow first List.mem_cons_self)
      intro next cap larger nextBelow
      apply ih
      · intro upper increase accumulator accumulatorBelow value member
        exact held upper (Nat.le_trans larger increase) accumulator accumulatorBelow value
          (List.mem_cons_of_mem _ member)
      · exact nextBelow

private def CandidatesBelow (bound : Nat) (candidates : Option (List Nat)) : Prop :=
  match candidates with
  | none => True
  | some keys => ∀ key ∈ keys, key < bound

private theorem zip_start (values : List α) (start : Nat) (pair : α × Nat)
    (member : pair ∈ values.zipIdx start) :
    pair.1 ∈ values ∧ pair.2 < start + values.length := by
  induction values generalizing start with
  | nil => simp at member
  | cons first rest ih =>
    rw [List.zipIdx_cons] at member
    rcases List.mem_cons.mp member with same | tail
    · cases same
      simp
    · obtain ⟨belongs, range⟩ := ih (start + 1) tail
      exact ⟨List.mem_cons_of_mem _ belongs, by simp only [List.length_cons]; omega⟩

/-- A listed indexed value has an existing value and an allocated list position. -/
private theorem zip_member (values : List α) (pair : α × Nat) (member : pair ∈ values.zipIdx) :
    pair.1 ∈ values ∧ pair.2 < values.length := by
  simpa using zip_start values 0 pair member

private theorem findExpandable_safe (graph : Graph Symbol Guard) (fuel : Nat) :
    Safe lower CandidatesBelow (EnumerationState.findExpandable graph fuel) := by
  unfold EnumerationState.findExpandable
  apply get_snapshot_safe
  intro snapshot indexed
  dsimp only
  apply bind_safe (pre := fun cap (pair : List Nat × List Nat) => ∀ key ∈ pair.1, key < cap)
  · apply foldlM_safe
    · intro lower upper pair larger held key member
      exact Nat.lt_of_lt_of_le (held key member) larger
    · intro cap growCap accumulator accumulatorBelow entry member
      rcases accumulator with ⟨candidates, blocked⟩
      rcases entry with ⟨value, index⟩
      have ⟨belongs, indexBelow⟩ := zip_member snapshot.values (value, index) member
      have indexInCounter : index < snapshot.counter := by
        simpa only [indexed.shape] using indexBelow
      have valueBelow := indexed.values value belongs
      dsimp only at accumulatorBelow ⊢
      cases value with
      | eliminated =>
          exact pure_safe (fun upper larger key member =>
            Nat.lt_of_lt_of_le (accumulatorBelow key member) larger)
      | enumerated fragment =>
          exact pure_safe (fun upper larger key member =>
            Nat.lt_of_lt_of_le (accumulatorBelow key member) larger)
      | unenumerated node scs =>
          apply bind_safe (pre := fun _ (_ : List Nat) => True)
          · apply foldlM_safe
            · intro lower upper value larger held
              trivial
            · intro currentCap growCurrent accumulator accumulatorBelow sc scMember
              apply bind_safe (safe_raise
                (representative_safe fuel sc.var (valueBelow sc scMember)) (by omega))
              intro root rootCap growRoot rootBelow
              exact pure_safe (fun _ _ => trivial)
            · trivial
          · intro resolved blockedCap growBlocked _
            split
            · apply pure_safe
              intro upper larger key member
              rcases List.mem_append.mp member with old | fresh
              · exact Nat.lt_of_lt_of_le (accumulatorBelow key old) (by omega)
              · cases List.mem_singleton.mp fresh
                omega
            · exact pure_safe (fun upper larger key member =>
                Nat.lt_of_lt_of_le (accumulatorBelow key member) (by omega))
    · intro key member
      simp at member
  · intro result cap growCap candidatesBelow
    rcases result with ⟨candidates, blocked⟩
    dsimp only
    split
    · exact pure_safe (fun _ _ => trivial)
    · apply pure_safe
      intro upper larger key member
      exact Nat.lt_of_lt_of_le (candidatesBelow key (List.mem_filter.mp member).1) larger

private theorem pickNext_below (preference : List Nat → Option Nat)
    (candidates : Option (List Nat)) (bounded : CandidatesBelow bound candidates)
    (key : Nat) (selected : EnumerationState.pickNext preference candidates = .expand key) :
    key < bound := by
  cases candidates with
  | none => simp [EnumerationState.pickNext] at selected
  | some candidates =>
      cases candidates with
      | nil => simp [EnumerationState.pickNext] at selected
      | cons first rest =>
          cases favored : preference (first :: rest) with
          | none =>
              have same : first = key := by simpa [EnumerationState.pickNext, favored] using selected
              exact same ▸ bounded first List.mem_cons_self
          | some chosen =>
              by_cases member : chosen ∈ first :: rest
              · have same : chosen = key := by
                  simpa [EnumerationState.pickNext, favored, member] using selected
                exact same ▸ bounded chosen member
              · have same : first = key := by
                  simpa [EnumerationState.pickNext, favored, member] using selected
                exact same ▸ bounded first List.mem_cons_self

private theorem out_safe (graph : Graph Symbol Guard) (fuel key : Nat) (below : key < lower) :
    Safe lower (fun cap fragment => FragmentBelow cap fragment)
      (EnumerationState.enumerateOut graph fuel key) := by
  intro before fragment after indexed lowerBound run
  exact EnumerationStateWorkerIndexValidity.enumerateOut_preserves_indices graph fuel key
    before fragment after indexed (Nat.lt_of_lt_of_le below lowerBound) run

private theorem pure_bind_eq (value : α) (next : α → EnumerateM Symbol Guard β) :
    ((pure value : EnumerateM Symbol Guard α) >>= next) = next value := by
  simp

private theorem fully_safe (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (fuel : Nat) :
    ∀ lower oracleState, Safe lower (fun _ _ => True)
      (EnumerationState.enumerateFully graph order oracle fuel oracleState) := by
  induction fuel with
  | zero =>
      intro lower oracleState
      exact failure_safe _
  | succ fuel ih =>
      intro lower oracleState
      simp only [EnumerationState.enumerateFully]
      apply bind_safe (findExpandable_safe graph (fuel + 1))
      intro candidates candidateCap growCandidates candidatesBelow
      cases chosen : EnumerationState.pickNext (order oracleState) candidates with
      | done => exact pure_safe (fun _ _ => trivial)
      | stuck => exact reject_safe
      | expand key =>
          have keyBelow : key < candidateCap := pickNext_below _ _ candidatesBelow key chosen
          apply bind_safe (getValue_safe (fuel + 1) key keyBelow)
          intro value valueCap growValue valueBelow
          cases value with
          | eliminated => exact reject_safe
          | enumerated fragment => exact reject_safe
          | unenumerated node scs =>
              cases node with
              | none => exact reject_safe
              | some node =>
                  dsimp only
                  cases view : graph.node node <;> dsimp only
                  case recursive body =>
                    apply bind_safe (representative_safe (fuel + 1) key (by omega))
                    intro root rootCap growRoot rootBelow
                    apply get_then_safe
                    intro snapshot
                    split
                    · apply bind_safe (setValue_safe root (.unenumerated (some node) []) (by
                        intro sc member
                        simp at member))
                      intro _ cap larger _
                      simpa using ih cap oracleState
                    ·
                      simp only [pure_bind_eq]
                      apply bind_safe (oracle_before_safe oracle law oracleState key node (by omega))
                      intro answer beforeCap growBefore _
                      rcases answer with ⟨beforeReject, beforeState⟩
                      apply bind_safe (require_safe _)
                      intro _ requiredCap growRequired _
                      apply bind_safe (out_safe graph (fuel + 1) key (by omega))
                      intro fragment expandedCap growExpanded fragmentBelow
                      apply bind_safe (oracle_after_safe oracle law beforeState key fragment
                        (by omega) fragmentBelow)
                      intro answer afterCap growAfter _
                      rcases answer with ⟨afterReject, afterState⟩
                      apply bind_safe (require_safe _)
                      intro _ finalCap growFinal _
                      exact ih finalCap afterState
                  all_goals
                    simp only [pure_bind_eq]
                    apply bind_safe (oracle_before_safe oracle law oracleState key node (by omega))
                    intro answer beforeCap growBefore _
                    rcases answer with ⟨beforeReject, beforeState⟩
                    apply bind_safe (require_safe _)
                    intro _ requiredCap growRequired _
                    apply bind_safe (out_safe graph (fuel + 1) key (by omega))
                    intro fragment expandedCap growExpanded fragmentBelow
                    apply bind_safe (oracle_after_safe oracle law beforeState key fragment
                      (by omega) fragmentBelow)
                    intro answer afterCap growAfter _
                    rcases answer with ⟨afterReject, afterState⟩
                    apply bind_safe (require_safe _)
                    intro _ finalCap growFinal _
                    exact ih finalCap afterState

/-- This internal theorem composes the actual worker with its callback law.
It does not establish that law for a native callback implementation. -/
theorem enumerateFully_preserves_indices (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (fuel : Nat) (oracleState : OracleState)
    (before after : EnumerationState.State Symbol Guard) (indexed : Indexed before)
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.enumerateFully graph order oracle fuel oracleState before)) :
    Indexed after ∧ before.counter ≤ after.counter := by
  obtain ⟨preserved, _, monotone⟩ := fully_safe graph order oracle law fuel 0 oracleState
    before () after indexed (Nat.zero_le _) returned
  exact ⟨preserved, monotone⟩

/-- Initialization discharges the state invariant under the internal callback law. -/
theorem enumerateFully_initial_indices (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (fuel root : Nat) (oracleState : OracleState)
    (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.enumerateFully graph order oracle fuel oracleState (EnumerationState.initial root))) :
    Indexed after ∧ 1 ≤ after.counter := by
  exact enumerateFully_preserves_indices graph order oracle law fuel oracleState
    (EnumerationState.initial root) after (initial_invariant root) returned

/-- An initial node result remains index-valid through the complete worker. -/
theorem initial_node_then_fully_indices (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (nodeFuel fullyFuel root : Nat) (oracleState : OracleState)
    (fragment : Fragments.Fragment Symbol) (middle after : EnumerationState.State Symbol Guard)
    (expanded : Except.ok (fragment, middle) ∈ ExceptT.run
      (EnumerationState.enumerateNode graph nodeFuel [] root (EnumerationState.initial root)))
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.enumerateFully graph order oracle fullyFuel oracleState middle)) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ 1 ≤ after.counter := by
  obtain ⟨indexed, references, positive⟩ := enumerateNode_initial_indices graph nodeFuel root fragment middle expanded
  obtain ⟨preserved, monotone⟩ := enumerateFully_preserves_indices graph order oracle law fullyFuel oracleState
    middle after indexed returned
  exact ⟨preserved, fragment_mono references monotone, by omega⟩

/-- An initial edge result remains index-valid through the complete worker. -/
theorem initial_edge_then_fully_indices (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (edgeFuel fullyFuel root : Nat) (oracleState : OracleState)
    (edge : Edge Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (middle after : EnumerationState.State Symbol Guard)
    (expanded : Except.ok (fragment, middle) ∈ ExceptT.run
      (EnumerationState.enumerateEdge graph edgeFuel [] edge (EnumerationState.initial root)))
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.enumerateFully graph order oracle fullyFuel oracleState middle)) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ 1 ≤ after.counter := by
  obtain ⟨indexed, references, positive⟩ := enumerateEdge_initial_indices graph edgeFuel root edge fragment middle expanded
  obtain ⟨preserved, monotone⟩ := enumerateFully_preserves_indices graph order oracle law fullyFuel oracleState
    middle after indexed returned
  exact ⟨preserved, fragment_mono references monotone, by omega⟩

/-- An initial actual step result remains index-valid through the complete worker. -/
theorem initial_out_then_fully_indices (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (law : OraclePreservesIndices oracle) (outFuel fullyFuel root : Nat) (oracleState : OracleState)
    (fragment : Fragments.Fragment Symbol) (middle after : EnumerationState.State Symbol Guard)
    (expanded : Except.ok (fragment, middle) ∈ ExceptT.run
      (EnumerationState.enumerateOut graph outFuel 0 (EnumerationState.initial root)))
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.enumerateFully graph order oracle fullyFuel oracleState middle)) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ 1 ≤ after.counter := by
  obtain ⟨indexed, references, positive⟩ := EnumerationStateWorkerIndexValidity.enumerateOut_initial_indices
    graph outFuel root fragment middle expanded
  obtain ⟨preserved, monotone⟩ := enumerateFully_preserves_indices graph order oracle law fullyFuel oracleState
    middle after indexed returned
  exact ⟨preserved, fragment_mono references monotone, by omega⟩

end MicroCFTA.EnumerationStateFullyIndexValidity
