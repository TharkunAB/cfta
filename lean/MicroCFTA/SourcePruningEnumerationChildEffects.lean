import MicroCFTA.SourcePruningEnumerationChildDispatch
import MicroCFTA.SourcePruningEnumerationStorage

namespace MicroCFTA.SourcePruningEnumerationChildEffects
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint

private theorem allocated_effects (node : Option Nat)
    (before : EnumerationState.State Symbol Constraint) (safe : Safe before) :
    Safe (allocated node before) ∧ EnumeratedOrigin before (allocated node before) ∧
    ∀ held, held < before.counter → IsRoot before.representatives held →
      EnumerationDriver.Protected held before (allocated node before) :=
  ⟨⟨allocation_storage node before safe.1, allocation_live node before safe.1 safe.2⟩,
    allocation_origin node before,
    fun held inside root => EnumerationDriver.allocation_protected held node before safe inside root⟩

private theorem fresh_write_effects (node : Option Nat) (scs : List Suspended)
    (before : EnumerationState.State Symbol Constraint) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter) :
    let after := {allocated node before with
      values := (allocated node before).values.set before.counter (.unenumerated node scs)}
    Safe after ∧ EnumeratedOrigin before after ∧
    ∀ held, held < before.counter → IsRoot before.representatives held →
      EnumerationDriver.Protected held before after := by
  dsimp only
  let after := {allocated node before with
    values := (allocated node before).values.set before.counter (.unenumerated node scs)}
  obtain ⟨allocatedSafe, origin, protects⟩ := allocated_effects node before safe
  have written : Success (setValue before.counter (.unenumerated node scs))
      (allocated node before) () after := (EnumerationDriver.modify_success _ _ _).mpr rfl
  have root : IsRoot before.representatives before.counter :=
    (allocatedSafe.2 before.counter (.unenumerated node [])
      (allocated_slot node before safe.1.aligned)).mp (by simp)
  refine ⟨(EnumerationDriver.setValue_safe before.counter (.unenumerated node scs)
    (allocated node before) after allocatedSafe root (by simp)
    (fun sc member => Nat.lt_trans (bounded sc member) (Nat.lt_succ_self _)) written).1,
    origin.trans (setValue_origin _ _ _ _ (by intros; simp) written), ?_⟩
  intro held inside heldRoot
  have prior := protects held inside heldRoot
  refine ⟨?_, prior.root, prior.classes⟩
  change ((allocated node before).values.set before.counter (.unenumerated node scs))[held]? = _
  rw [List.getElem?_set_ne (Nat.ne_of_gt inside)]
  exact prior.value

/-- An actual prepared child preserves safety and every old allocated root. -/
theorem child
    (scs : List Suspended) (value : Node)
    (action : EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
    (before after : EnumerationState.State Symbol Constraint)
    (fragment : Fragments.Fragment Symbol) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs value = some action)
    (observed : Success action before fragment after) :
    Safe after ∧ EnumeratedOrigin before after ∧
    ∀ held, held < before.counter → IsRoot before.representatives held →
      EnumerationDriver.Protected held before after := by
  cases value with
  | empty =>
    simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
    subst action
    exact (reject_unsuccessful before after fragment observed).elim
  | reference _name =>
    simp [SourcePruningEnumerationShallowChild.prepareChild] at prepared
  | node entry _edges _depth _free =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have shape : fragment = .hole before.counter ∧
        after = {allocated (some (entry.identity + 1)) before with
          values := (allocated (some (entry.identity + 1)) before).values.set before.counter
            (.unenumerated (some (entry.identity + 1)) scs)} := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [setValue, bind, pure, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.bind, StateT.pure, StateT.modifyGet, ExceptT.bind, ExceptT.pure,
        ExceptT.bindCont, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := shape
    exact fresh_write_effects _ scs before safe bounded
  | union entry _ _ _ | mu entry _ _ _ =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have shape : fragment = .hole before.counter ∧
        after = allocated (some (entry.identity + 1)) before := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := shape
    exact allocated_effects _ before safe

/-- A prepared child retains pending inputs for every later bucket. -/
theorem child_inputs
    (scs retained : List Suspended) (value : Node)
    (action : EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
    (before after : EnumerationState.State Symbol Constraint)
    (fragment : Fragments.Fragment Symbol) (safe : Safe before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (pending : InputsPending before retained)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs value = some action)
    (observed : Success action before fragment after) : InputsPending after retained := by
  obtain ⟨_afterSafe, origin, protects⟩ := child scs value action before after fragment safe bounded prepared observed
  intro held storedFragment stored
  have old := origin held storedFragment stored
  obtain ⟨inside, root⟩ := enumerated_root before safe held storedFragment old
  exact (protects held inside root).avoids retained (pending held storedFragment old)

/-- Origin and root protection retain the full bucket for later child descents. -/
theorem retained_inputs
    (before after : EnumerationState.State Symbol Constraint)
    (scs active : List Suspended) (safe : Safe before)
    (pending : InputsPending before scs)
    (descended : ∀ held, Avoids before.representatives held scs →
      Avoids before.representatives held active)
    (origin : EnumeratedOrigin before after)
    (protects : ∀ held, IsRoot before.representatives held →
      Avoids before.representatives held active → EnumerationDriver.Protected held before after) :
    InputsPending after scs := by
  intro held fragment stored
  have old := origin held fragment stored
  have root := (enumerated_root before safe held fragment old).2
  have avoids := pending held fragment old
  exact (protects held root (descended held avoids)).avoids scs avoids

/-- A terminal child retains the parent inputs for the next child descent. -/
theorem terminal_inputs
    (before after : EnumerationState.State Symbol Constraint)
    (scs : List Suspended) (index : Nat) (first : Suspended) (rest descendants : List Suspended)
    (safe : Safe before) (pending : InputsPending before scs)
    (partitioned : (descendScs index scs).partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants))
    (origin : EnumeratedOrigin before after)
    (protects : ∀ held, IsRoot before.representatives held →
      Avoids before.representatives held (first :: rest) → EnumerationDriver.Protected held before after) :
    InputsPending after scs := by
  apply retained_inputs before after scs (first :: rest) safe pending ?_ origin protects
  intro held avoids sc member
  apply descend_avoids before.representatives held index scs avoids sc
  have terminalMembers : (descendScs index scs).filter (fun sc => EqualityTrie.isTerminal sc.trie) =
      first :: rest := by
    simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
  exact (List.mem_filter.mp (terminalMembers ▸ member)).1

end MicroCFTA.SourcePruningEnumerationChildEffects
