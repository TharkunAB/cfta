import MicroCFTA.SourceCurrentSelectedStepCheckedTotal

namespace MicroCFTA.SourceCurrentSelectedStepObservedTotal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable [DecidableEq Symbol] [DecidableEq Node]

attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Preserve the selected-step result and prove totality for its action observation. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos) (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ readFuel checkFuel nativeFuel representativeFuel indexFuel,
      ∀ er ec ei callbackFuel r n p h k,
        let observed := SourcePruningEnumerationSelectedStep.run holeKey fits admits graph templates
          checkEmpty edgesOf stop order metadata (readFuel + er) (checkFuel + ec) nativeFuel
          representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos.query
        SourcePruningEnumerationSelectedStep.Valid holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (readFuel + er) (checkFuel + ec) nativeFuel
          representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos observed ∧
        match observed with
        | .narrowed checked _ _ _ action _ _ _ =>
            Frame before.core checked ∧ UnionFind.Total checked.representatives ∧
              match action with
              | some [.ok ((), after)] => UnionFind.Total after.representatives
              | _ => True
        | _ => True := by
  obtain ⟨readFuel, checkFuel, nativeFuel, representativeFuel, indexFuel, results⟩ :=
    SourceCurrentSelectedStepCheckedTotal.complete holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory caller memos before
      preference uv roots initial safe pending selection realized paths counts flags
  refine ⟨readFuel, checkFuel, nativeFuel, representativeFuel, indexFuel, ?_⟩
  intro er ec ei callbackFuel r n p h k
  have previous := results er ec ei callbackFuel r n p h k
  have setterRepresentatives (slot : Nat) (content : UVarValue Symbol)
      (input output : EnumerationState.State Symbol Constraint)
      (stored : Success (setValue slot content) input () output) :
      output.representatives = input.representatives := by
    dsimp only [Success, setValue, modify, instMonadStateOfMonadStateOf,
      MonadState.modifyGet, instMonadStateOfStateTOfMonad, MonadStateOf.modifyGet,
      StateT.modifyGet, Pure.pure, Applicative.toPure, Monad.toApplicative,
      ExceptT.instMonad, ExceptT.pure, ExceptT.run, ExceptT.mk,
      EnumerationState.instMonadList_microCFTA, Membership.mem, List.instMembership] at stored
    cases stored with
    | head => rfl
    | tail _ rest => nomatch rest
  have successfulSingleton (operation : EnumerateM Symbol Constraint Unit)
      (input output : EnumerationState.State Symbol Constraint)
      (raw : ExceptT.run (operation input) = [Except.ok ((), output)]) :
      Success operation input () output := by
    dsimp only [Success]
    rw [raw]
    dsimp only [Membership.mem, List.instMembership]
    exact List.Mem.head []
  have preparedTotal (oldHandle : Nat) (scs : List Suspended) (oldValue value : Node)
      (heap afterHeap : InternedConstructorTemplates.State Symbol Constraint)
      (operation : EnumerateM Symbol Constraint Unit)
      (input output : EnumerationState.State Symbol Constraint)
      (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
        representativeFuel uv oldHandle scs oldValue heap = .done (value, some operation) afterHeap)
      (total : UnionFind.Total input.representatives) (successful : Success operation input () output) :
      UnionFind.Total output.representatives := by
    dsimp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow] at prepared
    all_goals try (split at prepared)
    all_goals try (split at prepared)
    all_goals try (split at prepared)
    all_goals try (split at prepared)
    all_goals cases prepared
    all_goals first
    | solve
      | dsimp only [Success, reject, ExceptT.run, ExceptT.mk,
          Membership.mem, List.instMembership] at successful
        cases successful
    | exact (pure_frame _ _ _ _ successful).total total
    | have preserved := setterRepresentatives _ _ input output successful
      rw [preserved]
      exact total
    | obtain ⟨selected, intermediate, represented, stored⟩ :=
        (MicroCFTA.EnumerationCorrectness.success_bind
          (MicroCFTA.EnumerationState.representative representativeFuel uv) _ input () output).mp successful
      have frame := representative_frame representativeFuel uv selected input intermediate total represented
      have preserved := setterRepresentatives _ _ intermediate output stored
      rw [preserved]
      exact frame.total total
  let retain := fun observed : SourcePruningEnumerationSelectedStep.Result width Typing =>
    match observed with
    | .narrowed checked _ _ _ action _ _ _ => some (checked, action)
    | _ => none
  have finishRetains (observed : SourcePruningEnumerationSelectedStep.Result width Typing) :
      retain (SourcePruningEnumerationSelectedStep.finish checkEmpty edgesOf r n p h k uv observed) =
        retain observed := by
    cases observed with
    | stopped _ _ => rfl
    | parked _ _ _ => rfl
    | narrowed core prepared reached queries action candidate right ordinary =>
        cases candidate with
        | none => rfl
        | some attached =>
            cases right with
            | none => rfl
            | some rows =>
                cases rows with
                | nil => rfl
                | cons event rest =>
                    cases event with
                    | error _ => rfl
                    | ok item =>
                        rcases item with ⟨⟨flag, updated⟩, callback⟩
                        cases flag <;> cases rest <;> cases ordinary <;> rfl
  refine ⟨previous.1, ?_⟩
  have checked := previous.2
  generalize actual : SourcePruningEnumerationSelectedStep.run holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata (readFuel + er) (checkFuel + ec) nativeFuel
    representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos.query =
      produced at checked ⊢
  cases produced with
  | stopped _ _ => exact True.intro
  | parked _ _ _ => exact True.intro
  | narrowed core prepared reached queries action candidate right ordinary =>
      refine ⟨checked.1, checked.2, ?_⟩
      cases action with
      | none => exact True.intro
      | some raw =>
          cases raw with
          | nil => exact True.intro
          | cons first tail =>
              cases first with
              | error _ => exact True.intro
              | ok observed =>
                  cases observed with
                  | mk outcomeUnit afterState =>
                      cases outcomeUnit
                      cases tail with
                      | cons _ _ => exact True.intro
                      | nil =>
                          have currentTotal : UnionFind.Total core.representatives := checked.2
                          have observedAction := (finishRetains
                            (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
                              stop order metadata (readFuel + er) (checkFuel + ec) nativeFuel
                              representativeFuel (indexFuel + ei) callbackFuel uv caller before memos.query)).symm.trans
                            (congrArg retain actual)
                          dsimp only [SourcePruningEnumerationSelectedStep.runPrefix, SourcePruningEnumerationSelectedStep.runPrefixWithNarrow] at observedAction
                          all_goals try (split at observedAction)
                          all_goals try (split at observedAction)
                          all_goals try (split at observedAction)
                          all_goals try (split at observedAction)
                          all_goals try (split at observedAction)
                          all_goals try (split at observedAction)
                          all_goals try (split at observedAction)
                          all_goals try (split at observedAction)
                          all_goals dsimp only [retain] at observedAction
                          all_goals
                            have retainedShape := congrArg
                              (fun kept => match kept with
                                | some (_, some _) => some ()
                                | _ => none) observedAction
                            dsimp only at retainedShape
                            cases retainedShape
                          all_goals
                            have retainedCore := congrArg
                              (fun kept => match kept with
                                | some (selectedCore, _) => selectedCore
                                | none => core) observedAction
                            have retainedValues := congrArg
                              (fun kept => match kept with
                                | some (_, some values) => values
                                | _ => []) observedAction
                            dsimp only at retainedCore retainedValues
                            have inputTotal := currentTotal
                            rw [← retainedCore] at inputTotal
                            refine preparedTotal _ _ _ _ _ _ _ _ _ (by assumption) inputTotal ?_
                            · exact successfulSingleton _ _ _ retainedValues

end MicroCFTA.SourceCurrentSelectedStepObservedTotal
