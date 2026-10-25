import MicroCFTA.SourcePruningEnumerationDispatchShape
import MicroCFTA.SourcePruningEnumerationFold
import MicroCFTA.SourcePruningEnumerationShallowChild
import MicroCFTA.EnumerationReferences

namespace MicroCFTA.SourcePruningEnumerationNativeReferences
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Assimilation stores only references from its two actual pending slots. -/
theorem assimilated_allowed (allowed : Nat → Prop)
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (valid : ReferencesAllowed allowed before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs)) :
    ReferencesAllowed allowed (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
  have sourceInputs : InputsAllowed allowed sourceScs := valid _ (List.mem_of_getElem? sourceStored)
  have targetInputs : InputsAllowed allowed targetScs := valid _ (List.mem_of_getElem? targetStored)
  let middle := {before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))}
  have first : ReferencesAllowed allowed middle :=
    setValue_allowed allowed target _ before middle valid
      (fun sc member => (List.mem_append.mp member).elim (sourceInputs sc) (targetInputs sc))
      ((EnumerationDriver.modify_success _ _ _).mpr rfl)
  exact setValue_allowed allowed source .eliminated middle
    {middle with values := middle.values.set source .eliminated} first
    (by simp [InputsAllowed, references]) ((EnumerationDriver.modify_success _ _ _).mpr rfl)

/-- A native incoming write adds its supplied bucket to the actual current payload. -/
theorem incoming_written (allowed : Nat → Prop)
    (read after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (oldNode : Option Nat) (incomingScs oldScs : List Suspended)
    (valid : ReferencesAllowed allowed read) (inputs : InputsAllowed allowed incomingScs)
    (stored : read.values[target]? = some (.unenumerated oldNode oldScs))
    (written : after.values = read.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))) :
    ReferencesAllowed allowed after := by
  have oldInputs : InputsAllowed allowed oldScs := valid _ (List.mem_of_getElem? stored)
  intro value member
  rw [written] at member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid value old
  · subst value
    intro sc listed
    exact (List.mem_append.mp listed).elim (inputs sc) (oldInputs sc)

/-- An actual native dispatcher singleton retains the fixed allowed-reference predicate. -/
theorem dispatch_allowed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (allowed : Nat → Prop) (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries) (after : EnumerationState.State Symbol EnumGuard)
    (valid : ReferencesAllowed allowed before)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) : ReferencesAllowed allowed after := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨_different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact valid
  · exact assimilated_allowed allowed before source target sourceNode targetNode merged sourceScs targetScs
      valid sourceStored targetStored

/-- Every actual fold endpoint retains the fixed predicate, including rejection and faults. -/
theorem fold_allowed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (allowed : Nat → Prop) (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries) (after : EnumerationState.State Symbol EnumGuard)
    (valid : ReferencesAllowed allowed before)
    (observed : SourcePruningEnumerationFold.run checkEmpty nativeFuel p h sources
      beforeCaller before target queries = (result, afterCaller, savedQueries, after)) : ReferencesAllowed allowed after := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
    simp only [SourcePruningEnumerationFold.run, Prod.mk.injEq] at observed
    rcases observed with ⟨rfl, rfl, rfl, rfl⟩
    exact valid
  | cons source rest ih =>
    rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
    cases dispatchResult with
    | error fault =>
      simp only [SourcePruningEnumerationFold.run, dispatchObserved, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact valid
    | ok possible =>
      cases possible with
      | none =>
        simp only [SourcePruningEnumerationFold.run, dispatchObserved, Prod.mk.injEq] at observed
        rcases observed with ⟨rfl, rfl, rfl, rfl⟩
        exact valid
      | some action =>
        cases rawObserved : ExceptT.run (action before) with
        | nil =>
          simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact valid
        | cons head tail =>
          cases head with
          | error error =>
            simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
            rcases observed with ⟨rfl, rfl, rfl, rfl⟩
            exact valid
          | ok pair =>
            rcases pair with ⟨valueUnit, middle⟩
            cases valueUnit
            cases tail with
            | nil =>
              have middleValid := dispatch_allowed allowed checkEmpty nativeFuel p h beforeCaller before
                source target queries action reachedCaller saved middle valid dispatchObserved rawObserved
              simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved] at observed
              exact ih reachedCaller middle saved middleValid observed
            | cons second remaining =>
              simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact valid

/-- A prepared shallow child stores only its supplied suspended references. -/
theorem prepared_allowed (allowed : Nat → Prop) (scs : List Suspended) (value : Node)
    (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
    (before after : EnumerationState.State Symbol EnumGuard) (fragment : Fragments.Fragment Symbol)
    (valid : ReferencesAllowed allowed before) (inputs : InputsAllowed allowed scs)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs value = some action)
    (observed : Success action before fragment after) : ReferencesAllowed allowed after := by
  cases value with
  | empty =>
    simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
    subst action
    exact (reject_unsuccessful before after fragment observed).elim
  | reference _name => simp [SourcePruningEnumerationShallowChild.prepareChild] at prepared
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
    exact setValue_allowed allowed before.counter (.unenumerated (some (entry.identity + 1)) scs)
      (allocated (some (entry.identity + 1)) before) _ (allocation_allowed allowed _ before valid) inputs
      ((EnumerationDriver.modify_success _ _ _).mpr rfl)
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
    exact allocation_allowed allowed _ before valid

end MicroCFTA.SourcePruningEnumerationNativeReferences
