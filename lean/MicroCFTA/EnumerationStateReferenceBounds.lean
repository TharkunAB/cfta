import MicroCFTA.EnumerationStateExpansionBounds
import MicroCFTA.EqualityTrieVariableOrigin
import MicroCFTA.UnionFindTotalPreservation

set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateReferenceBounds

open EnumerationState UnionFindSupport
open EnumerationStateExpansionBounds (totalCost maxCost)

variable {Symbol Guard α β : Type}

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

/-- Each suspended variable is below the bound. -/
def SuspensionsBelow (bound : Nat) (scs : List Suspended) : Prop :=
  ∀ entry ∈ scs, entry.var < bound

/-- Each hole in the constructed fragment is below the bound. -/
inductive FragmentBelow (bound : Nat) : Fragments.Fragment Symbol → Prop where
  | hole (key : Nat) (below : key < bound) : FragmentBelow bound (.hole key)
  | node (symbol : Symbol) (children : List (Fragments.Fragment Symbol))
      (below : ∀ child ∈ children, FragmentBelow bound child) :
      FragmentBelow bound (.node symbol children)

/-- Each variable reference in a stored value is below the bound. -/
def ValueBelow (bound : Nat) : UVarValue Symbol → Prop
  | .unenumerated _ scs => SuspensionsBelow bound scs
  | .enumerated fragment => FragmentBelow bound fragment
  | .eliminated => True

/-- The state uses one internal bound for its counter and variable references. -/
structure Invariant (bound : Nat) (state : EnumerationState.State Symbol Guard) : Prop where
  counter : state.counter ≤ bound
  shape : state.values.length = state.counter
  supported : SupportedBelow bound state.representatives
  parents : ParentsBelow bound state.representatives
  total : UnionFind.Total state.representatives
  values : ∀ value ∈ state.values, ValueBelow bound value
  obligations : ∀ entry ∈ state.obligations, FragmentBelow bound entry.2

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

/-- An increased internal bound preserves the state invariant. -/
theorem invariant_mono (held : Invariant lower state) (larger : lower ≤ upper) :
    Invariant upper state := by
  exact ⟨Nat.le_trans held.counter larger, held.shape,
    supportedBelow_mono held.supported larger, parentsBelow_mono held.parents larger,
    held.total,
    fun value member => value_mono (held.values value member) larger,
    fun entry member => fragment_mono (held.obligations entry member) larger⟩

/-- Initial model states have no outgoing variable references. -/
theorem initial_invariant (root : Nat) :
    Invariant 1 (EnumerationState.initial root : EnumerationState.State Symbol Guard) := by
  obtain ⟨_, shape, supported, parents, total⟩ :=
    EnumerationStateAllocation.initial_invariants (Symbol := Symbol) (Guard := Guard) root
  refine ⟨by simp [EnumerationState.initial], shape, supported, parents, total, ?_, ?_⟩
  · simp [EnumerationState.initial, ValueBelow, SuspensionsBelow]
  · simp [EnumerationState.initial]

private def Safe (bound cost : Nat) (post : α → Prop)
    (action : EnumerateM Symbol Guard α) : Prop :=
  ∀ before value after, Invariant bound before → before.counter + cost ≤ bound →
    Except.ok (value, after) ∈ ExceptT.run (action before) →
    Invariant bound after ∧ post value ∧ before.counter ≤ after.counter ∧
      after.counter ≤ before.counter + cost

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

private theorem safe_mono (held : Safe bound lower post action) (larger : lower ≤ upper) :
    Safe bound upper post action := by
  intro before value after state capacity run
  obtain ⟨preserved, result, monotone, limited⟩ := held before value after state (by omega) run
  exact ⟨preserved, result, monotone, by omega⟩

private theorem pure_safe (held : post value) :
    Safe bound 0 post (pure value : EnumerateM Symbol Guard α) := by
  intro before result after state capacity run
  change Except.ok (result, after) ∈ [Except.ok (value, before)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
  exact ⟨state, held, Nat.le_refl _, Nat.le_refl _⟩

private theorem bind_safe (first : Safe bound left pre action)
    (next : ∀ value, pre value → Safe bound right post (following value)) :
    Safe bound (left + right) post (action >>= following) := by
  intro before value after state capacity run
  obtain ⟨result, middle, firstRun, nextRun⟩ := (mem_bind _ _ _ _ _).mp run
  obtain ⟨middleState, firstValue, firstMono, firstBound⟩ :=
    first before result middle state (by omega) firstRun
  obtain ⟨afterState, resultValue, nextMono, nextBound⟩ :=
    next result firstValue middle value after middleState (by omega) nextRun
  exact ⟨afterState, resultValue, by omega, by omega⟩

private theorem bind_zero_left (first : Safe bound 0 pre action)
    (next : ∀ value, pre value → Safe bound cost post (following value)) :
    Safe bound cost post (action >>= following) := by
  simpa only [Nat.zero_add] using bind_safe first next

private theorem bind_zero_right (first : Safe bound cost pre action)
    (next : ∀ value, pre value → Safe bound 0 post (following value)) :
    Safe bound cost post (action >>= following) := by
  simpa only [Nat.add_zero] using bind_safe first next

private theorem failure_safe (error : EnumerationState.Error) :
    Safe bound cost post (EnumerationState.failure error : EnumerateM Symbol Guard α) := by
  intro before value after state capacity run
  change Except.ok (value, after) ∈ [Except.error error] at run
  simp at run

private theorem reject_safe :
    Safe bound cost post (EnumerationState.reject : EnumerateM Symbol Guard α) := by
  intro before value after state capacity run
  change Except.ok (value, after) ∈ [] at run
  simp at run

private theorem require_safe (condition : Bool) :
    Safe bound 0 (fun _ => True) (EnumerationState.require condition : EnumerateM Symbol Guard Unit) := by
  cases condition with
  | false => exact reject_safe
  | true => exact pure_safe trivial

private theorem modify_safe (change : EnumerationState.State Symbol Guard → EnumerationState.State Symbol Guard)
    (preserves : ∀ state, Invariant bound state → Invariant bound (change state))
    (counter : ∀ state, (change state).counter = state.counter) :
    Safe bound 0 (fun _ => True) (modify change : EnumerateM Symbol Guard Unit) := by
  intro before value after state capacity run
  change Except.ok (value, after) ∈ [Except.ok ((), change before)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  have equal := congrArg Prod.snd paired
  dsimp only at equal
  subst after
  exact ⟨preserves before state, trivial, by rw [counter]; omega, by rw [counter]; omega⟩

private theorem get_bind_safe
    (next : EnumerationState.State Symbol Guard → EnumerateM Symbol Guard α)
    (held : ∀ before value after, Invariant bound before → before.counter + cost ≤ bound →
      Except.ok (value, after) ∈ ExceptT.run (next before before) →
      Invariant bound after ∧ post value ∧ before.counter ≤ after.counter ∧
        after.counter ≤ before.counter + cost) :
    Safe bound cost post ((get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) >>= next) := by
  intro before value after state capacity run
  obtain ⟨snapshot, middle, got, continued⟩ := (mem_bind _ _ _ _ _).mp run
  change Except.ok (snapshot, middle) ∈ [Except.ok (before, before)] at got
  have paired := Except.ok.inj (List.mem_singleton.mp got)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
  exact held _ value after state capacity continued

private theorem allocate_safe (node : Option Nat) :
    Safe bound 1 (fun key => key < bound)
      (EnumerationState.allocate node : EnumerateM Symbol Guard Nat) := by
  intro before value after state capacity run
  change Except.ok (value, after) ∈ [Except.ok (before.counter, _)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  have valueEqual := congrArg Prod.fst paired
  have stateEqual := congrArg Prod.snd paired
  dsimp only at valueEqual stateEqual
  subst value after
  refine ⟨?_, by omega, by simp, by simp⟩
  refine ⟨capacity, ?_, state.supported, state.parents, state.total, ?_, state.obligations⟩
  · simp [state.shape]
  · intro value member
    change value ∈ before.values ++ [_] at member
    rcases List.mem_append.mp member with old | fresh
    · exact state.values value old
    · cases List.mem_singleton.mp fresh
      simp [ValueBelow, SuspensionsBelow]

/-- A successful suspension stays below the internal cap. -/
theorem suspend_safe (trie : EqualityTrie.Trie) :
    ∀ (before : EnumerationState.State Symbol Guard) (value : Suspended)
      (after : EnumerationState.State Symbol Guard),
      Invariant bound before → before.counter + 1 ≤ bound →
      Except.ok (value, after) ∈ ExceptT.run (EnumerationState.suspend trie before) →
      Invariant bound after ∧ value.var < bound ∧ before.counter ≤ after.counter ∧
        after.counter ≤ before.counter + 1 := by
  have preserved : Safe bound 1 (fun value : Suspended => value.var < bound)
      (EnumerationState.suspend trie : EnumerateM Symbol Guard Suspended) := by
    unfold EnumerationState.suspend
    apply bind_zero_right (allocate_safe _)
    intro key below
    exact pure_safe below
  exact preserved

private theorem representative_safe (fuel key : Nat) (below : key < bound) :
    Safe bound 0 (fun result => result < bound)
      (EnumerationState.representative fuel key : EnumerateM Symbol Guard Nat) := by
  unfold EnumerationState.representative
  apply get_bind_safe
  intro before value after state capacity run
  cases found : UnionFind.findRoot fuel before.representatives key with
  | none =>
      simp only [found] at run
      exact failure_safe (post := fun result : Nat => result < bound) _
        before value after state capacity run
  | some result =>
      simp only [found] at run
      change Except.ok (value, after) ∈ [Except.ok (result.representative, _)] at run
      have paired := Except.ok.inj (List.mem_singleton.mp run)
      have valueEqual := congrArg Prod.fst paired
      have stateEqual := congrArg Prod.snd paired
      dsimp only at valueEqual stateEqual
      subst value after
      obtain ⟨supported, parents, resultBelow⟩ :=
        findRoot_preserves_bounds bound fuel before.representatives key
          state.supported state.parents below result found
      exact ⟨⟨state.counter, state.shape, supported, parents,
        UnionFind.findRoot_total state.total found, state.values, state.obligations⟩,
        resultBelow, Nat.le_refl _, Nat.le_refl _⟩

/-- Successful representative queries retain the internal bound. -/
theorem representative_preserves_references (fuel key : Nat) (below : key < bound) :
    ∀ (before : EnumerationState.State Symbol Guard) (value : Nat)
      (after : EnumerationState.State Symbol Guard),
      Invariant bound before →
      Except.ok (value, after) ∈ ExceptT.run (EnumerationState.representative fuel key before) →
      Invariant bound after ∧ value < bound ∧ before.counter = after.counter := by
  intro before value after state run
  obtain ⟨preserved, result, monotone, limited⟩ :=
    representative_safe fuel key below before value after state (by simpa using state.counter) run
  exact ⟨preserved, result, by omega⟩

private theorem union_safe (fuel left right : Nat) (leftBelow : left < bound) (rightBelow : right < bound) :
    Safe bound 0 (fun _ => True)
      (EnumerationState.unionVariables fuel left right : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.unionVariables
  apply get_bind_safe
  intro before value after state capacity run
  cases united : UnionFind.union fuel fuel before.representatives left right with
  | none =>
      simp only [united] at run
      exact failure_safe (post := fun _ : Unit => True) _
        before value after state capacity run
  | some forest =>
      simp only [united] at run
      change Except.ok (value, after) ∈ [Except.ok ((), _)] at run
      have paired := Except.ok.inj (List.mem_singleton.mp run)
      have stateEqual := congrArg Prod.snd paired
      dsimp only at stateEqual
      subst after
      obtain ⟨supported, parents⟩ :=
        union_preserves_bounds bound fuel fuel before.representatives left right
          state.supported state.parents leftBelow rightBelow forest united
      exact ⟨⟨state.counter, state.shape, supported, parents,
        UnionFindTotalPreservation.union_preserves_total before.representatives forest
          fuel fuel left right state.total united, state.values, state.obligations⟩,
        trivial, Nat.le_refl _, Nat.le_refl _⟩

/-- Successful variable unions retain the internal bound. -/
theorem unionVariables_preserves_references (fuel left right : Nat)
    (leftBelow : left < bound) (rightBelow : right < bound) :
    ∀ (before : EnumerationState.State Symbol Guard) (value : Unit)
      (after : EnumerationState.State Symbol Guard),
      Invariant bound before →
      Except.ok (value, after) ∈ ExceptT.run (EnumerationState.unionVariables fuel left right before) →
      Invariant bound after ∧ before.counter = after.counter := by
  intro before value after state run
  obtain ⟨preserved, _, monotone, limited⟩ :=
    union_safe fuel left right leftBelow rightBelow before value after state (by simpa using state.counter) run
  exact ⟨preserved, by omega⟩

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

private theorem setValue_safe (key : Nat) (value : UVarValue Symbol) (held : ValueBelow bound value) :
    Safe bound 0 (fun _ => True) (EnumerationState.setValue key value : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.setValue
  apply modify_safe
  · intro state invariant
    refine ⟨invariant.counter, ?_, invariant.supported, invariant.parents, invariant.total,
      ?_, invariant.obligations⟩
    · simpa using invariant.shape
    · exact set_preserves_all _ _ _ _ invariant.values held
  · intro state
    rfl

private theorem inherit_safe (key : Nat) :
    Safe bound 0 (fun _ => True) (EnumerationState.inheritAncestry key : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.inheritAncestry
  apply modify_safe
  · intro state invariant
    exact ⟨invariant.counter, invariant.shape, invariant.supported, invariant.parents,
      invariant.total, invariant.values, invariant.obligations⟩
  · intro state
    rfl

private theorem rawValue_safe (key : Nat) :
    Safe bound 0 (ValueBelow bound)
      (EnumerationState.rawValue key : EnumerateM Symbol Guard (UVarValue Symbol)) := by
  unfold EnumerationState.rawValue
  apply get_bind_safe
  intro before value after state capacity run
  cases looked : before.values[key]? with
  | none =>
      simp only [looked] at run
      exact failure_safe _ before value after state capacity run
  | some cell =>
      simp only [looked] at run
      exact pure_safe (state.values cell (lookup_is_member _ _ _ looked))
        before value after state capacity run

private theorem getValue_safe (fuel key : Nat) (below : key < bound) :
    Safe bound 0 (ValueBelow bound)
      (EnumerationState.getValue fuel key : EnumerateM Symbol Guard (UVarValue Symbol)) := by
  unfold EnumerationState.getValue
  apply bind_zero_left (representative_safe fuel key below)
  intro root rootBelow
  exact rawValue_safe root

private theorem intersectValues_below (graph : Graph Symbol Guard)
    (left right : UVarValue Symbol) (leftBelow : ValueBelow bound left)
    (rightBelow : ValueBelow bound right) (result : UVarValue Symbol)
    (returned : EnumerationState.intersectValues graph left right = some result) :
    ValueBelow bound result := by
  cases left <;> cases right <;>
    simp_all [EnumerationState.intersectValues, ValueBelow, SuspensionsBelow] <;> grind

private theorem assimilate_safe (graph : Graph Symbol Guard) (target source : Nat) :
    Safe bound 0 (fun _ => True) (EnumerationState.assimilate graph target source) := by
  unfold EnumerationState.assimilate
  split
  · exact pure_safe trivial
  · apply bind_zero_left (rawValue_safe source)
    intro sourceValue sourceBelow
    cases sourceValue
    case eliminated => exact pure_safe trivial
    all_goals
      apply bind_zero_left (rawValue_safe target)
      intro targetValue targetBelow
      split
      · exact failure_safe _
      · rename_i merged matched
        have mergedBelow : ValueBelow bound merged := by
          apply intersectValues_below (returned := matched) <;> assumption
        apply bind_zero_left (require_safe _)
        intro _ _
        apply bind_zero_left (setValue_safe target merged mergedBelow)
        intro _ _
        apply bind_zero_left (setValue_safe source .eliminated trivial)
        intro _ _
        apply modify_safe
        · intro state invariant
          exact ⟨invariant.counter, invariant.shape, invariant.supported, invariant.parents,
            invariant.total, invariant.values, invariant.obligations⟩
        · intro state
          rfl

private theorem mergeNode_safe (graph : Graph Symbol Guard) (fuel key node : Nat)
    (scs : List Suspended) (keyBelow : key < bound) (scsBelow : SuspensionsBelow bound scs) :
    Safe bound 0 (fun _ => True) (EnumerationState.mergeNode graph fuel key node scs) := by
  unfold EnumerationState.mergeNode
  apply bind_zero_left (representative_safe fuel key keyBelow)
  intro root rootBelow
  apply bind_zero_left (rawValue_safe root)
  intro previous previousBelow
  have incoming : ValueBelow bound (.unenumerated (some node) scs : UVarValue Symbol) := scsBelow
  split
  · exact failure_safe _
  · rename_i merged matched
    have mergedBelow : ValueBelow bound merged := by
      apply intersectValues_below (returned := matched) <;> assumption
    apply bind_zero_left (setValue_safe root merged mergedBelow)
    intro _ _
    apply bind_zero_left (inherit_safe root)
    intro _ _
    exact require_safe _

private theorem cost_le_max (cost : α → Nat) (member : value ∈ values) :
    cost value ≤ maxCost cost values := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | present
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

private theorem mapM_cons_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (action : α → m β) (first : α) (rest : List α) :
    (first :: rest).mapM action =
      (do let value ← action first; let tail ← rest.mapM action; pure (value :: tail)) := by
  simp

private theorem mapM_safe (values : List α) (action : α → EnumerateM Symbol Guard β)
    (cost : α → Nat) (post : β → Prop)
    (held : ∀ value ∈ values, Safe bound (cost value) post (action value)) :
    Safe bound (totalCost cost values) (fun results => ∀ value ∈ results, post value)
      (values.mapM action) := by
  induction values with
  | nil =>
      apply pure_safe
      simp
  | cons first rest ih =>
      rw [mapM_cons_eq]
      change Safe bound (cost first + totalCost cost rest) _ _
      apply bind_safe (held first (List.mem_cons_self))
      intro head headBelow
      apply bind_zero_right (ih (fun value member => held value (List.mem_cons_of_mem _ member)))
      intro tail tailBelow
      apply pure_safe
      intro value member
      rcases List.mem_cons.mp member with rfl | present
      · exact headBelow
      · exact tailBelow value present

private theorem totalCost_zero (values : List α) : totalCost (fun _ : α => 0) values = 0 := by
  induction values <;> simp_all [totalCost]

private theorem totalCost_one (values : List α) : totalCost (fun _ : α => 1) values = values.length := by
  induction values <;> simp_all [totalCost] <;> omega

private theorem mapM_zero_safe (values : List α) (action : α → EnumerateM Symbol Guard β)
    (post : β → Prop) (held : ∀ value ∈ values, Safe bound 0 post (action value)) :
    Safe bound 0 (fun results => ∀ value ∈ results, post value) (values.mapM action) := by
  simpa only [totalCost_zero] using mapM_safe values action (fun _ => 0) post held

private theorem forM_safe (values : List α) (action : α → EnumerateM Symbol Guard Unit)
    (held : ∀ value ∈ values, Safe bound 0 (fun _ => True) (action value)) :
    Safe bound 0 (fun _ => True) (values.forM action) := by
  induction values with
  | nil => exact pure_safe trivial
  | cons first rest ih =>
      change Safe bound 0 (fun _ => True) (do action first; rest.forM action)
      apply bind_zero_left (held first (List.mem_cons_self))
      intro _ _
      exact ih (fun value member => held value (List.mem_cons_of_mem _ member))

private theorem choose_bind_safe (values : List α) (next : α → EnumerateM Symbol Guard β)
    (cost : α → Nat) (held : ∀ value ∈ values, Safe bound (cost value) post (next value)) :
    Safe bound (maxCost cost values) post (EnumerationState.choose values >>= next) := by
  intro before value after state capacity run
  obtain ⟨selected, middle, chosen, continued⟩ := (mem_bind _ _ _ _ _).mp run
  change Except.ok (selected, middle) ∈ values.map (fun choice => Except.ok (choice, before)) at chosen
  obtain ⟨choice, member, paired⟩ := List.mem_map.mp chosen
  have equal := Except.ok.inj paired
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact safe_mono (held _ member) (cost_le_max _ member) _ value after state capacity continued

private theorem suspensions_safe (tries : List EqualityTrie.Trie) :
    Safe bound tries.length (fun results => SuspensionsBelow bound results)
      (tries.mapM EnumerationState.suspend : EnumerateM Symbol Guard (List Suspended)) := by
  simpa only [totalCost_one, SuspensionsBelow] using
    mapM_safe tries EnumerationState.suspend (fun _ => 1)
      (fun value : Suspended => value.var < bound) (fun trie _ => suspend_safe trie)

private theorem terminal_node_safe (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (references : SuspensionsBelow bound scs)
    (present : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) ≠ []) :
    Safe bound 0 (FragmentBelow bound)
      (EnumerationState.enumerateNode graph (fuel + 1) scs node) := by
  cases selected : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
  | nil => exact False.elim (present selected)
  | cons first rest =>
      have hereBelow : SuspensionsBelow bound (first :: rest) := by
        intro entry member
        apply references entry
        apply (List.mem_filter.mp (show entry ∈ scs.filter _ from by rw [selected]; exact member)).1
      have firstBelow : first.var < bound := hereBelow first (List.mem_cons_self)
      cases view : graph.node node <;>
        simp only [EnumerationState.enumerateNode, view, selected]
      case empty => exact reject_safe
      all_goals
        apply bind_zero_left (mapM_zero_safe _ _ (fun key : Nat => key < bound)
          (fun entry member => representative_safe _ _ (hereBelow entry member)))
        intro roots rootsBelow
        apply bind_zero_left
        · apply forM_safe
          intro entry member
          exact union_safe _ _ _ firstBelow
            (hereBelow entry (List.mem_cons_of_mem _ member))
        · intro _ _
          apply bind_zero_left (representative_safe _ _ firstBelow)
          intro root rootBelow
          apply bind_zero_left (forM_safe _ _ (fun _ _ => assimilate_safe _ _ _))
          intro _ _
          apply bind_zero_left (mergeNode_safe _ _ _ _ _ rootBelow (by
            intro entry member
            exact references entry (List.mem_filter.mp member).1))
          intro _ _
          exact pure_safe (FragmentBelow.hole _ rootBelow)

private theorem expansion_safe (bound : Nat) (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node, SuspensionsBelow bound scs →
      Safe bound (EnumerationStateExpansionBounds.nodeAllocationBudget graph fuel node)
        (FragmentBelow bound) (EnumerationState.enumerateNode graph fuel scs node)) ∧
    (∀ scs edge, SuspensionsBelow bound scs →
      Safe bound (EnumerationStateExpansionBounds.edgeAllocationBudget graph fuel edge)
        (FragmentBelow bound) (EnumerationState.enumerateEdge graph fuel scs edge)) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node references
        exact failure_safe _
      · intro scs edge references
        exact failure_safe _
  | succ fuel ih =>
      obtain ⟨nodeIH, edgeIH⟩ := ih
      constructor
      · intro scs node references
        by_cases absent : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = []
        · cases view : graph.node node <;>
            simp only [EnumerationStateExpansionBounds.nodeAllocationBudget,
              EnumerationState.enumerateNode, view, absent]
          case empty => exact reject_safe
          case unresolved => exact failure_safe _
          case recursive body =>
            apply bind_zero_right (allocate_safe _)
            intro key below
            exact pure_safe (FragmentBelow.hole _ below)
          case alternatives edges =>
            exact choose_bind_safe edges
              (fun edge => EnumerationState.enumerateEdge graph fuel scs edge)
              (EnumerationStateExpansionBounds.edgeAllocationBudget graph fuel)
              (fun edge _ => edgeIH scs edge references)
        · exact safe_mono (terminal_node_safe graph fuel node scs references absent) (Nat.zero_le _)
      · intro scs edge references
        simp only [EnumerationStateExpansionBounds.edgeAllocationBudget, EnumerationState.enumerateEdge]
        apply bind_zero_left (require_safe _)
        intro _ _
        apply bind_safe (suspensions_safe edge.equalities)
        intro added addedBelow
        have combined : SuspensionsBelow bound (scs ++ added) := by
          intro entry member
          rcases List.mem_append.mp member with old | fresh
          · exact references entry old
          · exact addedBelow entry fresh
        apply bind_zero_right
        · exact mapM_safe edge.children.zipIdx
            (fun child => EnumerationState.enumerateNode graph fuel
              (EnumerationState.descendScs child.2 (scs ++ added)) child.1)
            (fun child : Nat × Nat =>
              EnumerationStateExpansionBounds.nodeAllocationBudget graph fuel child.1)
            (FragmentBelow bound)
            (fun child _ => nodeIH _ _
              (EqualityTrieVariableOrigin.descendScs_preserves_below child.2 bound _ combined))
        · intro children childrenBelow
          split
          · exact pure_safe (FragmentBelow.node _ _ childrenBelow)
          · apply bind_zero_left
            · apply modify_safe
              · intro state invariant
                refine ⟨invariant.counter, invariant.shape, invariant.supported, invariant.parents,
                  invariant.total, invariant.values, ?_⟩
                intro entry member
                change entry ∈ _ :: state.obligations at member
                rcases List.mem_cons.mp member with rfl | old
                · exact FragmentBelow.node _ _ childrenBelow
                · exact invariant.obligations entry old
              · intro state
                rfl
            · intro _ _
              exact pure_safe (FragmentBelow.node _ _ childrenBelow)


/-- Successful node expansion preserves a fixed internal cap. -/
theorem enumerateNode_preserves_fixed_cap (cap : Nat) (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (before : EnumerationState.State Symbol Guard)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (state : Invariant cap before) (references : SuspensionsBelow cap scs)
    (capacity : before.counter + EnumerationStateExpansionBounds.nodeAllocationBudget graph fuel node ≤ cap)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateNode graph fuel scs node before)) :
    Invariant cap after ∧ FragmentBelow cap fragment := by
  obtain ⟨preserved, result, _, _⟩ :=
    (expansion_safe cap graph fuel).1 scs node references before fragment after state capacity returned
  exact ⟨preserved, result⟩

/-- Successful edge expansion preserves a fixed internal cap. -/
theorem enumerateEdge_preserves_fixed_cap (cap : Nat) (graph : Graph Symbol Guard) (fuel : Nat)
    (edge : Edge Symbol Guard) (scs : List Suspended)
    (before : EnumerationState.State Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard) (state : Invariant cap before)
    (references : SuspensionsBelow cap scs)
    (capacity : before.counter + EnumerationStateExpansionBounds.edgeAllocationBudget graph fuel edge ≤ cap)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateEdge graph fuel scs edge before)) :
    Invariant cap after ∧ FragmentBelow cap fragment := by
  obtain ⟨preserved, result, _, _⟩ :=
    (expansion_safe cap graph fuel).2 scs edge references before fragment after state capacity returned
  exact ⟨preserved, result⟩

/-- Suspension returns the old counter and creates one value slot. -/
theorem suspend_fresh (trie : EqualityTrie.Trie) (before : EnumerationState.State Symbol Guard)
    (value : Suspended) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (value, after) ∈ ExceptT.run (EnumerationState.suspend trie before)) :
    value.var = before.counter ∧ after.counter = before.counter + 1 ∧
      after.values.length = before.values.length + 1 := by
  change Except.ok (value, after) ∈ [Except.ok (_, _)] at returned
  have paired := Except.ok.inj (List.mem_singleton.mp returned)
  have valueEqual := congrArg Prod.fst paired
  have stateEqual := congrArg Prod.snd paired
  dsimp only at valueEqual stateEqual
  subst value after
  refine ⟨rfl, rfl, ?_⟩
  simp

/-- A suspension variable is an actual value index when the incoming shape holds. -/
theorem suspend_valid_index (trie : EqualityTrie.Trie) (before : EnumerationState.State Symbol Guard)
    (value : Suspended) (after : EnumerationState.State Symbol Guard)
    (shape : before.values.length = before.counter)
    (returned : Except.ok (value, after) ∈ ExceptT.run (EnumerationState.suspend trie before)) :
    value.var < after.values.length := by
  obtain ⟨key, _, length⟩ := suspend_fresh trie before value after returned
  omega

/-- A successful node expansion preserves references below its computed allocation cap. -/
theorem enumerateNode_references_below_budget (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (before : EnumerationState.State Symbol Guard)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (state : Invariant before.counter before) (references : SuspensionsBelow before.counter scs)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateNode graph fuel scs node before)) :
    let cap := before.counter + EnumerationStateExpansionBounds.nodeAllocationBudget graph fuel node
    Invariant cap after ∧ FragmentBelow cap fragment := by
  dsimp
  let cap := before.counter + EnumerationStateExpansionBounds.nodeAllocationBudget graph fuel node
  have grows : before.counter ≤ cap := by dsimp [cap]; omega
  have enlarged := invariant_mono state grows
  have inputs := suspensions_mono references grows
  obtain ⟨preserved, result, _, _⟩ :=
    (expansion_safe cap graph fuel).1 scs node inputs before fragment after enlarged (Nat.le_refl _) returned
  exact ⟨preserved, result⟩

/-- A successful edge expansion preserves references below its computed allocation cap. -/
theorem enumerateEdge_references_below_budget (graph : Graph Symbol Guard) (fuel : Nat)
    (edge : Edge Symbol Guard) (scs : List Suspended)
    (before : EnumerationState.State Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard) (state : Invariant before.counter before)
    (references : SuspensionsBelow before.counter scs)
    (returned : Except.ok (fragment, after) ∈
      ExceptT.run (EnumerationState.enumerateEdge graph fuel scs edge before)) :
    let cap := before.counter + EnumerationStateExpansionBounds.edgeAllocationBudget graph fuel edge
    Invariant cap after ∧ FragmentBelow cap fragment := by
  dsimp
  let cap := before.counter + EnumerationStateExpansionBounds.edgeAllocationBudget graph fuel edge
  have grows : before.counter ≤ cap := by dsimp [cap]; omega
  have enlarged := invariant_mono state grows
  have inputs := suspensions_mono references grows
  obtain ⟨preserved, result, _, _⟩ :=
    (expansion_safe cap graph fuel).2 scs edge inputs before fragment after enlarged (Nat.le_refl _) returned
  exact ⟨preserved, result⟩

/-- The initial node case needs no supplied reference invariant or capacity. -/
theorem enumerateNode_initial_references (graph : Graph Symbol Guard) (fuel root : Nat)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateNode graph fuel [] root (EnumerationState.initial root))) :
    let cap := 1 + EnumerationStateExpansionBounds.nodeAllocationBudget graph fuel root
    Invariant cap after ∧ FragmentBelow cap fragment := by
  exact enumerateNode_references_below_budget graph fuel root [] (EnumerationState.initial root)
    fragment after (initial_invariant root) (by intro entry member; simp at member) returned

/-- The initial edge case needs no supplied reference invariant or capacity. -/
theorem enumerateEdge_initial_references (graph : Graph Symbol Guard) (fuel root : Nat)
    (edge : Edge Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateEdge graph fuel [] edge (EnumerationState.initial root))) :
    let cap := 1 + EnumerationStateExpansionBounds.edgeAllocationBudget graph fuel edge
    Invariant cap after ∧ FragmentBelow cap fragment := by
  exact enumerateEdge_references_below_budget graph fuel edge [] (EnumerationState.initial root)
    fragment after (initial_invariant root) (by intro entry member; simp at member) returned

/-- The actual representative action succeeds at the computed forest fuel. -/
theorem representative_computed_fuel {Symbol Guard : Type}
    (state : EnumerationState.State Symbol Guard) (bound key : Nat)
    (supported : SupportedBelow bound state.representatives)
    (total : UnionFind.Total state.representatives) :
    ∃ value after, Except.ok (value, after) ∈ ExceptT.run
      (EnumerationState.representative (bound + 1) key state) := by
  obtain ⟨found, run⟩ := findRoot_uniformFuel supported total key
  refine ⟨found.representative, { state with representatives := found.forest }, ?_⟩
  unfold EnumerationState.representative
  apply (mem_bind _ _ _ _ _).mpr
  refine ⟨state, state, ?_, ?_⟩
  · change Except.ok (state, state) ∈ [Except.ok (state, state)]
    exact List.mem_singleton_self _
  · rw [run]
    change Except.ok _ ∈ [Except.ok _]
    exact List.mem_singleton_self _

/-- The actual bounded union action succeeds at the same computed fuel. -/
theorem unionVariables_computed_fuel {Symbol Guard : Type}
    (state : EnumerationState.State Symbol Guard) (bound left right : Nat)
    (supported : SupportedBelow bound state.representatives)
    (parents : ParentsBelow bound state.representatives)
    (total : UnionFind.Total state.representatives)
    (leftBelow : left < bound) (rightBelow : right < bound) :
    ∃ after, Except.ok ((), after) ∈ ExceptT.run
      (EnumerationState.unionVariables (bound + 1) left right state) := by
  obtain ⟨forest, run, _, _, _⟩ :=
    UnionFindTotalPreservation.union_bounded_uniformFuel bound state.representatives
      left right supported parents total leftBelow rightBelow
  refine ⟨{ state with representatives := forest }, ?_⟩
  unfold EnumerationState.unionVariables
  apply (mem_bind _ _ _ _ _).mpr
  refine ⟨state, state, ?_, ?_⟩
  · change Except.ok (state, state) ∈ [Except.ok (state, state)]
    exact List.mem_singleton_self _
  · rw [run]
    change Except.ok _ ∈ [Except.ok _]
    exact List.mem_singleton_self _

end MicroCFTA.EnumerationStateReferenceBounds
