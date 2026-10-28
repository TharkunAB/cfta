import MicroCFTA.SourcePruningEnumerationAssimilation
import MicroCFTA.SourcePruningEnumerationDispatch
import MicroCFTA.EnumerationGraphReferences

/-!
# Carrier preservation through actual native pending assimilation

The source and target already belong to one union-find class.
The actual optional and checked branches retain any old graph handle.
The source write therefore transfers its carrier to the target.
-/
namespace MicroCFTA.SourcePruningEnumerationAssimilation
open EnumerationState EnumerationCorrectness EnumerationCarriers EnumerationGraphReferences
open EnumerationDependencies
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}

/-- Two actual pending writes retain all carriers and stored reference provenance. -/
theorem assimilated_carriers
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (total : UnionFind.Total before.representatives)
    (related : UnionFind.SameClass before.representatives target source)
    (references : ReferencesCarry before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (different : source ≠ target)
    (noneOrigin : merged = none → sourceNode = none ∧ targetNode = none) :
    let after := assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))
    after.representatives = before.representatives ∧ UnionFind.Total after.representatives ∧
      PreservesCarriers before after ∧ ReferencesCarry after := by
  have sourceInside := (List.getElem?_eq_some_iff.mp sourceStored).1
  have targetInside := (List.getElem?_eq_some_iff.mp targetStored).1
  have replacementBearing :
      GraphValue (.unenumerated sourceNode sourceScs : UVarValue Symbol) ∨
        GraphValue (.unenumerated targetNode targetScs : UVarValue Symbol) →
      GraphValue (.unenumerated merged (sourceScs ++ targetScs) : UVarValue Symbol) := by
    intro bearing
    cases merged with
    | some handle => trivial
    | none =>
        obtain ⟨sourceNone, targetNone⟩ := noneOrigin rfl
        rcases bearing with sourceBearing | targetBearing
        · simpa only [sourceNone, GraphValue] using sourceBearing
        · simpa only [targetNone, GraphValue] using targetBearing
  have preserved : PreservesCarriers before
      (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
    rintro uv ⟨held, value, same, stored, bearing⟩
    by_cases atSource : held = source
    · subst held
      have valueSame : value = .unenumerated sourceNode sourceScs :=
        Option.some.inj (stored.symm.trans sourceStored)
      refine ⟨target, .unenumerated merged (sourceScs ++ targetScs),
        UnionFind.sameClass_trans same (UnionFind.sameClass_symm related), ?_, ?_⟩
      · simp [assimilated, targetInside, different]
      · exact replacementBearing (.inl (valueSame ▸ bearing))
    · by_cases atTarget : held = target
      · subst held
        have valueSame : value = .unenumerated targetNode targetScs :=
          Option.some.inj (stored.symm.trans targetStored)
        refine ⟨target, .unenumerated merged (sourceScs ++ targetScs), same, ?_, ?_⟩
        · simp [assimilated, targetInside, different]
        · exact replacementBearing (.inr (valueSame ▸ bearing))
      · exact ⟨held, value, same,
          (assimilation_frame before target source held _ atTarget atSource).trans stored, bearing⟩
  have origin : EnumeratedOrigin before
      (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
    intro uv fragment stored
    by_cases atSource : uv = source
    · subst uv
      simp [assimilated, sourceInside] at stored
    · by_cases atTarget : uv = target
      · subst uv
        simp [assimilated, targetInside, different] at stored
      · exact (assimilation_frame before target source uv _ atTarget atSource).symm.trans stored
  exact ⟨rfl, total, preserved,
    references_transport before _ references preserved origin rfl⟩

/-- Actual nonempty native finish transfers the source carrier to its equal target. -/
theorem finish_carriers
    (before after : EnumerationState.State Symbol EnumGuard) (source target resultHandle : Nat)
    (sourceNode targetNode : Option Nat) (sourceScs targetScs : List Suspended)
    (result : InternedConstructorTemplates.Value Symbol
      (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (total : UnionFind.Total before.representatives)
    (related : UnionFind.SameClass before.representatives target source)
    (references : ReferencesCarry before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (different : source ≠ target)
    (success : Success (finish source target resultHandle sourceScs targetScs result) before () after) :
    after.representatives = before.representatives ∧ UnionFind.Total after.representatives ∧
      PreservesCarriers before after ∧ ReferencesCarry after := by
  cases result <;> first
    | exact (EnumerationSchedule.reject_unsuccessful before after () success).elim
    | have endpoint : after = assimilated before target source
          (.unenumerated (some resultHandle) (sourceScs ++ targetScs)) := by
        change Except.ok ((), after) ∈ [Except.ok ((), assimilated before target source
          (.unenumerated (some resultHandle) (sourceScs ++ targetScs)))] at success
        simpa only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq, true_and] using success
      rw [endpoint]
      exact assimilated_carriers before source target sourceNode targetNode (some resultHandle)
        sourceScs targetScs total related references sourceStored targetStored different
        (by intro impossible; cases impossible)

end MicroCFTA.SourcePruningEnumerationAssimilation

namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness EnumerationCarriers EnumerationGraphReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Each actual singleton transfers its eliminated source carrier within the recorded class. -/
theorem dispatch_carriers
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (total : UnionFind.Total before.representatives)
    (related : UnionFind.SameClass before.representatives target source)
    (references : ReferencesCarry before)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    after.representatives = before.representatives ∧ UnionFind.Total after.representatives ∧
      PreservesCarriers before after ∧ ReferencesCarry after := by
  by_cases same : source = target
  · simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_left same, Id.run, pure,
      Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
    rcases selected with ⟨rfl, rfl, rfl⟩
    change [Except.ok ((), before)] = [Except.ok ((), after)] at completed
    simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
    subst after
    exact ⟨rfl, total, .refl before, references⟩
  · cases sourceStored : before.values[source]? with
    | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored] at selected
    | some sourceValue =>
      cases sourceValue with
      | eliminated =>
        simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, Id.run, pure,
          Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
        rcases selected with ⟨rfl, rfl, rfl⟩
        change [Except.ok ((), before)] = [Except.ok ((), after)] at completed
        simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
        subst after
        exact ⟨rfl, total, .refl before, references⟩
      | enumerated sourceFragment =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
            Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
          rcases selected with ⟨rfl, rfl, rfl⟩
          cases completed
      | unenumerated sourceNode sourceScs =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          cases targetValue with
          | eliminated =>
            simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            cases completed
          | enumerated targetFragment =>
            simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            cases completed
          | unenumerated targetNode targetScs =>
            cases sourceNodeSame : sourceNode with
            | none =>
              subst sourceNode
              simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
              rcases selected with ⟨rfl, rfl, rfl⟩
              by_cases empty : targetNode = some 0
              · simp [SourcePruningEnumerationDispatch.finishOptional, empty, ExceptT.run] at completed
              · change (if targetNode = some 0 then [] else
                  [Except.ok ((), assimilated before target source (.unenumerated targetNode (sourceScs ++ targetScs)))]) = _ at completed
                rw [ite_eq_right empty] at completed
                simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                subst after
                exact SourcePruningEnumerationAssimilation.assimilated_carriers before source target none targetNode targetNode sourceScs targetScs
                  total related references sourceStored targetStored same (fun absent => ⟨rfl, absent⟩)
            | some sourceHandle =>
              subst sourceNode
              cases targetNodeSame : targetNode with
              | none =>
                subst targetNode
                simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                  Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                rcases selected with ⟨rfl, rfl, rfl⟩
                by_cases empty : (some sourceHandle : Option Nat) = some 0
                · simp [SourcePruningEnumerationDispatch.finishOptional, empty, ExceptT.run] at completed
                · change (if (some sourceHandle : Option Nat) = some 0 then [] else
                    [Except.ok ((), assimilated before target source (.unenumerated (some sourceHandle) (sourceScs ++ targetScs)))]) = _ at completed
                  rw [ite_eq_right empty] at completed
                  simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                  subst after
                  exact SourcePruningEnumerationAssimilation.assimilated_carriers before source target (some sourceHandle) none (some sourceHandle)
                    sourceScs targetScs total related references sourceStored targetStored same (by intro impossible; cases impossible)
              | some targetHandle =>
                subst targetNode
                cases leftDecoded : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap sourceHandle with
                | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded] at selected
                | some left =>
                  cases rightDecoded : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                  | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded] at selected
                  | some right =>
                    cases native : SourceEqualityNativeDemand.execute nativeFuel
                        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                    | yielded control checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | failed nativeFailure checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | constraintError message checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | blocked reason control checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | done query queried =>
                      rcases phase : (if checkEmpty then
                        SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (.done false queried beforeCaller.fourth, queries)) with ⟨worker, workerQueries⟩
                      cases workerSame : worker with
                      | failed fault checkedAfter saved =>
                        subst worker
                        simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded,
                          rightDecoded, native, SourcePruningEnumerationDispatch.afterQuery, phase, Except.mapError] at selected
                      | done answer checkedAfter saved =>
                        subst worker
                        cases encoded : SourcePruningEnumerationNodes.encodeNode (if answer then (.empty : Node) else query) with
                        | none =>
                          simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded,
                            rightDecoded, native, SourcePruningEnumerationDispatch.afterQuery, phase, encoded, Except.mapError] at selected
                        | some handle =>
                          simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                            leftDecoded, rightDecoded, native, SourcePruningEnumerationDispatch.afterQuery, phase,
                            encoded, Option.map_some, Except.mapError, Id.run, pure,
                            Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                          rcases selected with ⟨rfl, rfl, rfl⟩
                          revert completed
                          cases (if answer then (.empty : Node) else query) with
                          | empty => intro completed; cases completed
                          | reference name =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact SourcePruningEnumerationAssimilation.assimilated_carriers before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs total related references sourceStored targetStored same (by intro impossible; cases impossible)
                          | node entry edges depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact SourcePruningEnumerationAssimilation.assimilated_carriers before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs total related references sourceStored targetStored same (by intro impossible; cases impossible)
                          | union entry members depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact SourcePruningEnumerationAssimilation.assimilated_carriers before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs total related references sourceStored targetStored same (by intro impossible; cases impossible)
                          | mu entry body depthShape ordinaryShape =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact SourcePruningEnumerationAssimilation.assimilated_carriers before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs total related references sourceStored targetStored same (by intro impossible; cases impossible)


end MicroCFTA.SourcePruningEnumerationDispatch
