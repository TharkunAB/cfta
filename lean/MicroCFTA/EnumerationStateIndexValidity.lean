import MicroCFTA.EnumerationStateReferenceBounds

set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateIndexValidity

open EnumerationState EnumerationStateReferenceBounds UnionFindSupport

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

/-- Stored references and forest entries stay below the current value count. -/
def Indexed (state : EnumerationState.State Symbol Guard) : Prop :=
  Invariant state.counter state

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

private theorem allocate_safe (node : Option Nat) :
    Safe lower (fun cap key => key < cap)
      (EnumerationState.allocate node : EnumerateM Symbol Guard Nat) := by
  intro before value after state lowerBound run
  change Except.ok (value, after) ∈ [Except.ok (before.counter, _)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  have valueEqual := congrArg Prod.fst paired
  have stateEqual := congrArg Prod.snd paired
  dsimp only at valueEqual stateEqual
  subst value after
  refine ⟨?_, by simp, by simp⟩
  refine ⟨Nat.le_refl _, ?_, supportedBelow_mono state.supported (Nat.le_succ _),
    parentsBelow_mono state.parents (Nat.le_succ _), state.total, ?_, ?_⟩
  · simp [state.shape]
  · intro value member
    change value ∈ before.values ++ [_] at member
    rcases List.mem_append.mp member with old | fresh
    · exact value_mono (state.values value old) (Nat.le_succ _)
    · cases List.mem_singleton.mp fresh
      simp [ValueBelow, SuspensionsBelow]
  · intro entry member
    exact fragment_mono (state.obligations entry member) (Nat.le_succ _)

private theorem suspend_safe (trie : EqualityTrie.Trie) :
    Safe lower (fun cap (value : Suspended) => value.var < cap)
      (EnumerationState.suspend trie : EnumerateM Symbol Guard Suspended) := by
  unfold EnumerationState.suspend
  apply bind_safe (allocate_safe _)
  intro key cap larger below
  exact pure_safe (fun upper increase => Nat.lt_of_lt_of_le below increase)

private theorem representative_safe (fuel key : Nat) (below : key < lower) :
    Safe lower (fun cap result => result < cap)
      (EnumerationState.representative fuel key : EnumerateM Symbol Guard Nat) := by
  intro before value after state lowerBound run
  obtain ⟨preserved, result, counter⟩ :=
    EnumerationStateReferenceBounds.representative_preserves_references fuel key
      (Nat.lt_of_lt_of_le below lowerBound) before value after state run
  exact ⟨by simpa only [Indexed, ← counter] using preserved, by omega, by omega⟩

private theorem union_safe (fuel left right : Nat) (leftBelow : left < lower) (rightBelow : right < lower) :
    Safe lower (fun _ _ => True)
      (EnumerationState.unionVariables fuel left right : EnumerateM Symbol Guard Unit) := by
  intro before value after state lowerBound run
  obtain ⟨preserved, counter⟩ :=
    EnumerationStateReferenceBounds.unionVariables_preserves_references fuel left right
      (Nat.lt_of_lt_of_le leftBelow lowerBound) (Nat.lt_of_lt_of_le rightBelow lowerBound)
      before value after state run
  exact ⟨by simpa only [Indexed, ← counter] using preserved, trivial, by omega⟩

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

private theorem inherit_safe (key : Nat) :
    Safe lower (fun _ _ => True) (EnumerationState.inheritAncestry key : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.inheritAncestry
  apply modify_safe
  · intro before state lowerBound
    exact ⟨state.counter, state.shape, state.supported, state.parents,
      state.total, state.values, state.obligations⟩
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

private theorem intersectValues_below (graph : Graph Symbol Guard)
    (left right : UVarValue Symbol) (leftBelow : ValueBelow lower left)
    (rightBelow : ValueBelow lower right) (result : UVarValue Symbol)
    (returned : EnumerationState.intersectValues graph left right = some result) :
    ValueBelow lower result := by
  cases left <;> cases right <;>
    simp_all [EnumerationState.intersectValues, ValueBelow, SuspensionsBelow] <;> grind

private theorem assimilate_safe (graph : Graph Symbol Guard) (target source : Nat) :
    Safe lower (fun _ _ => True) (EnumerationState.assimilate graph target source) := by
  unfold EnumerationState.assimilate
  split
  · exact pure_safe (fun _ _ => trivial)
  · apply bind_safe (rawValue_safe source)
    intro sourceValue sourceCap growSource sourceBelow
    cases sourceValue
    case eliminated => exact pure_safe (fun _ _ => trivial)
    all_goals
      apply bind_safe (rawValue_safe target)
      intro targetValue targetCap growTarget targetBelow
      split
      · exact failure_safe _
      · rename_i merged matched
        have mergedBelow : ValueBelow targetCap merged := by
          apply intersectValues_below (returned := matched)
          · exact value_mono sourceBelow growTarget
          · exact targetBelow
        apply bind_safe (require_safe _)
        intro _ requireCap growRequire _
        apply bind_safe (setValue_safe target merged (value_mono mergedBelow growRequire))
        intro _ storedCap growStored _
        apply bind_safe (setValue_safe source .eliminated trivial)
        intro _ eliminatedCap growEliminated _
        apply modify_safe
        · intro state invariant lowerBound
          exact ⟨invariant.counter, invariant.shape, invariant.supported, invariant.parents,
            invariant.total, invariant.values, invariant.obligations⟩
        · intro state
          rfl

private theorem mergeNode_safe (graph : Graph Symbol Guard) (fuel key node : Nat)
    (scs : List Suspended) (keyBelow : key < lower) (scsBelow : SuspensionsBelow lower scs) :
    Safe lower (fun _ _ => True) (EnumerationState.mergeNode graph fuel key node scs) := by
  unfold EnumerationState.mergeNode
  apply bind_safe (representative_safe fuel key keyBelow)
  intro root rootCap growRoot rootBelow
  apply bind_safe (rawValue_safe root)
  intro previous valueCap growValue previousBelow
  have incoming : ValueBelow valueCap (.unenumerated (some node) scs : UVarValue Symbol) := by
    exact suspensions_mono scsBelow (by omega)
  split
  · exact failure_safe _
  · rename_i merged matched
    have mergedBelow : ValueBelow valueCap merged := by
      apply intersectValues_below (returned := matched) <;> assumption
    apply bind_safe (setValue_safe root merged mergedBelow)
    intro _ storedCap growStored _
    apply bind_safe (inherit_safe root)
    intro _ inheritedCap growInherited _
    exact require_safe _

private theorem mapM_cons_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (action : α → m β) (first : α) (rest : List α) :
    (first :: rest).mapM action =
      (do let value ← action first; let tail ← rest.mapM action; pure (value :: tail)) := by
  simp

private theorem mapM_safe (values : List α) (action : α → EnumerateM Symbol Guard β)
    (post : Nat → β → Prop)
    (grows : ∀ lower upper value, lower ≤ upper → post lower value → post upper value)
    (held : ∀ value ∈ values, Safe lower post (action value)) :
    Safe lower (fun cap results => ∀ value ∈ results, post cap value) (values.mapM action) := by
  induction values with
  | nil =>
      apply pure_safe
      intro cap larger value member
      simp at member
  | cons first rest ih =>
      rw [mapM_cons_eq]
      apply bind_safe (held first List.mem_cons_self)
      intro head headCap growHead headBelow
      apply bind_safe (safe_raise
        (ih (fun value member => held value (List.mem_cons_of_mem _ member))) growHead)
      intro tail tailCap growTail tailBelow
      apply pure_safe
      intro cap larger value member
      rcases List.mem_cons.mp member with rfl | present
      · exact grows _ _ _ (Nat.le_trans growTail larger) headBelow
      · exact grows _ _ _ larger (tailBelow value present)

private theorem forM_safe (values : List α) (action : α → EnumerateM Symbol Guard Unit)
    (held : ∀ value ∈ values, Safe lower (fun _ _ => True) (action value)) :
    Safe lower (fun _ _ => True) (values.forM action) := by
  induction values with
  | nil => exact pure_safe (fun _ _ => trivial)
  | cons first rest ih =>
      change Safe lower (fun _ _ => True) (do action first; rest.forM action)
      apply bind_safe (held first List.mem_cons_self)
      intro _ cap larger _
      exact safe_raise (ih (fun value member => held value (List.mem_cons_of_mem _ member))) larger

private theorem choose_bind_safe (values : List α) (next : α → EnumerateM Symbol Guard β)
    (held : ∀ value ∈ values, Safe lower post (next value)) :
    Safe lower post (EnumerationState.choose values >>= next) := by
  intro before value after state lowerBound run
  obtain ⟨selected, middle, chosen, continued⟩ := (mem_bind _ _ _ _ _).mp run
  change Except.ok (selected, middle) ∈ values.map (fun choice => Except.ok (choice, before)) at chosen
  obtain ⟨choice, member, paired⟩ := List.mem_map.mp chosen
  have equal := Except.ok.inj paired
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact held _ member _ value after state lowerBound continued

private theorem suspensions_safe (tries : List EqualityTrie.Trie) :
    Safe lower (fun cap results => SuspensionsBelow cap results)
      (tries.mapM EnumerationState.suspend : EnumerateM Symbol Guard (List Suspended)) := by
  simpa only [SuspensionsBelow] using
    mapM_safe tries EnumerationState.suspend (fun cap (value : Suspended) => value.var < cap)
      (fun _ _ _ larger below => Nat.lt_of_lt_of_le below larger) (fun trie _ => suspend_safe trie)

private theorem terminal_node_safe (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (references : SuspensionsBelow lower scs)
    (present : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) ≠ []) :
    Safe lower (fun cap fragment => FragmentBelow cap fragment)
      (EnumerationState.enumerateNode graph (fuel + 1) scs node) := by
  cases selected : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
  | nil => exact False.elim (present selected)
  | cons first rest =>
      have hereBelow : SuspensionsBelow lower (first :: rest) := by
        intro entry member
        apply references entry
        exact (List.mem_filter.mp (show entry ∈ scs.filter _ from by rw [selected]; exact member)).1
      have firstBelow : first.var < lower := hereBelow first List.mem_cons_self
      cases view : graph.node node <;>
        simp only [EnumerationState.enumerateNode, view, selected]
      case empty => exact reject_safe
      all_goals
        apply bind_safe (mapM_safe _ _ (fun cap key : Nat => key < cap)
          (fun _ _ _ larger below => Nat.lt_of_lt_of_le below larger)
          (fun entry member => representative_safe _ _ (hereBelow entry member)))
        intro roots rootsCap growRoots rootsBelow
        apply bind_safe
        · apply forM_safe
          intro entry member
          exact safe_raise (union_safe _ _ _ firstBelow
            (hereBelow entry (List.mem_cons_of_mem _ member))) growRoots
        · intro _ unitedCap growUnited _
          apply bind_safe (safe_raise (representative_safe _ _ firstBelow) (by omega))
          intro root rootCap growRoot rootBelow
          apply bind_safe (forM_safe _ _ (fun _ _ => assimilate_safe _ _ _))
          intro _ assimilatedCap growAssimilated _
          apply bind_safe (mergeNode_safe _ _ _ _ _
            (Nat.lt_of_lt_of_le rootBelow growAssimilated) (by
              apply suspensions_mono (lower := lower)
              · intro entry member
                exact references entry (List.mem_filter.mp member).1
              · omega))
          intro _ mergedCap growMerged _
          exact pure_safe (fun cap larger => FragmentBelow.hole root (by omega))

private theorem expansion_safe (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ lower scs node, SuspensionsBelow lower scs →
      Safe lower (fun cap fragment => FragmentBelow cap fragment)
        (EnumerationState.enumerateNode graph fuel scs node)) ∧
    (∀ lower scs edge, SuspensionsBelow lower scs →
      Safe lower (fun cap fragment => FragmentBelow cap fragment)
        (EnumerationState.enumerateEdge graph fuel scs edge)) := by
  induction fuel with
  | zero =>
      constructor
      · intro lower scs node references
        exact failure_safe _
      · intro lower scs edge references
        exact failure_safe _
  | succ fuel ih =>
      obtain ⟨nodeIH, edgeIH⟩ := ih
      constructor
      · intro lower scs node references
        by_cases absent : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = []
        · cases view : graph.node node <;> simp only [EnumerationState.enumerateNode, view, absent]
          case empty => exact reject_safe
          case unresolved => exact failure_safe _
          case recursive body =>
            apply bind_safe (allocate_safe _)
            intro key cap larger below
            exact pure_safe (fun upper increase => FragmentBelow.hole key (Nat.lt_of_lt_of_le below increase))
          case alternatives edges =>
            exact choose_bind_safe edges
              (fun edge => EnumerationState.enumerateEdge graph fuel scs edge)
              (fun edge _ => edgeIH lower scs edge references)
        · exact terminal_node_safe graph fuel node scs references absent
      · intro lower scs edge references
        simp only [EnumerationState.enumerateEdge]
        apply bind_safe (require_safe _)
        intro _ requiredCap growRequired _
        apply bind_safe (suspensions_safe edge.equalities)
        intro added addedCap growAdded addedBelow
        have combined : SuspensionsBelow addedCap (scs ++ added) := by
          intro entry member
          rcases List.mem_append.mp member with old | fresh
          · exact Nat.lt_of_lt_of_le (references entry old) (by omega)
          · exact addedBelow entry fresh
        apply bind_safe
        · exact mapM_safe edge.children.zipIdx
            (fun child => EnumerationState.enumerateNode graph fuel
              (EnumerationState.descendScs child.2 (scs ++ added)) child.1)
            (fun cap fragment => FragmentBelow cap fragment)
            (fun _ _ _ larger below => fragment_mono below larger)
            (fun child _ => nodeIH addedCap _ _
              (EqualityTrieVariableOrigin.descendScs_preserves_below child.2 addedCap _ combined))
        · intro children childrenCap growChildren childrenBelow
          split
          · exact pure_safe (fun cap larger => FragmentBelow.node _ _
              (fun child member => fragment_mono (childrenBelow child member) larger))
          · apply bind_safe
            · apply modify_safe
              · intro state invariant lowerBound
                refine ⟨invariant.counter, invariant.shape, invariant.supported, invariant.parents,
                  invariant.total, invariant.values, ?_⟩
                intro entry member
                change entry ∈ _ :: state.obligations at member
                rcases List.mem_cons.mp member with rfl | old
                · exact FragmentBelow.node _ _
                    (fun child member => fragment_mono (childrenBelow child member) lowerBound)
                · exact invariant.obligations entry old
              · intro state
                rfl
            · intro _ storedCap growStored _
              exact pure_safe (fun cap larger => FragmentBelow.node _ _
                (fun child member => fragment_mono (childrenBelow child member) (by omega)))

/-- Successful node expansion preserves actual current-counter reference validity. -/
theorem enumerateNode_preserves_indices (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (before : EnumerationState.State Symbol Guard)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (state : Indexed before) (references : SuspensionsBelow before.counter scs)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateNode graph fuel scs node before)) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ before.counter ≤ after.counter := by
  exact (expansion_safe graph fuel).1 before.counter scs node references
    before fragment after state (Nat.le_refl _) returned

/-- Successful edge expansion preserves actual current-counter reference validity. -/
theorem enumerateEdge_preserves_indices (graph : Graph Symbol Guard) (fuel : Nat)
    (edge : Edge Symbol Guard) (scs : List Suspended)
    (before : EnumerationState.State Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard) (state : Indexed before)
    (references : SuspensionsBelow before.counter scs)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateEdge graph fuel scs edge before)) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ before.counter ≤ after.counter := by
  exact (expansion_safe graph fuel).2 before.counter scs edge references
    before fragment after state (Nat.le_refl _) returned

/-- The actual initial node case needs no supplied validity or capacity. -/
theorem enumerateNode_initial_indices (graph : Graph Symbol Guard) (fuel root : Nat)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateNode graph fuel [] root (EnumerationState.initial root))) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ 1 ≤ after.counter := by
  exact enumerateNode_preserves_indices graph fuel root [] (EnumerationState.initial root)
    fragment after (initial_invariant root) (by intro entry member; simp at member) returned

/-- The actual initial edge case needs no supplied validity or capacity. -/
theorem enumerateEdge_initial_indices (graph : Graph Symbol Guard) (fuel root : Nat)
    (edge : Edge Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateEdge graph fuel [] edge (EnumerationState.initial root))) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ 1 ≤ after.counter := by
  exact enumerateEdge_preserves_indices graph fuel edge [] (EnumerationState.initial root)
    fragment after (initial_invariant root) (by intro entry member; simp at member) returned

end MicroCFTA.EnumerationStateIndexValidity
