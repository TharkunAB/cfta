import MicroCFTA.SourcePruningEnumerationRendering
import MicroCFTA.EnumerationGraphReferences

/-!
# A free hole outside native rendering provenance

This finite core has safe, canonical and proper storage and is discharged.
Its completed root refers to a free equality slot without a graph carrier.
This is a pure-state counterexample. It is not an actual startup history.
-/
namespace MicroCFTA.SourcePruningEnumerationFreeHole
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationValidity EnumerationProgress EnumerationCarriers EnumerationGraphReferences
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Core" => EnumerationState.State Symbol Unit

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private def symbol : Symbol := ("x", .top)
private def state : Core :=
  ⟨2, UnionFind.withInitialValues [0, 1],
    [.enumerated (.node symbol [.hole 1]), .unenumerated none []], [], fun _ => [], []⟩
private def assignment (uv : Nat) : Term Symbol :=
  if uv = 0 then .node symbol [.node symbol []] else .node symbol []

/-- A discharged safe core can contain an unrenderable free hole without native history provenance. -/
theorem free_hole_counterexample :
    ∃ before : Core,
      Safe before ∧ Canonical before ∧ ProperState before ∧
      SourcePruningEnumerationRendering.Discharged before ∧
      (∃ model : Nat → Term Symbol, Satisfies (fun _ _ => True) (fun _ _ => True) model before) ∧
      CarriesGraph before 0 ∧ ¬ CarriesGraph before 1 ∧ ¬ ReferencesCarry before ∧
      ∀ (heap : InternedConstructorTemplates.State Symbol Unit) (marker : Symbol)
        (fuel : Nat) (term : Term Symbol) (pending : List (Unit × Term Symbol)) (after : Core),
        ¬ Success (SourcePruningEnumerationRendering.render heap marker fuel 0)
          before (term, pending) after := by
  have storage : StorageValid state := by
    refine ⟨rfl, UnionFind.initial_total [0, 1], ?_, ?_, by simp [state]⟩
    · intro uv entry stored
      simp only [state, UnionFind.withInitialValues] at stored
      split at stored
      · rename_i member
        simp only [List.mem_cons, List.mem_singleton] at member
        rcases member with rfl | rfl <;> cases stored <;> simp
      · cases stored
    · intro value member
      simp only [state, List.mem_cons, List.mem_singleton] at member
      rcases member with rfl | rfl <;>
        simp [SlotBound, FragmentBound, FragmentsBound]
  have live : LiveRoots state := by
    intro uv value stored
    have root : IsRoot state.representatives uv := ⟨1, .root (UnionFind.read_initial [0, 1] uv)⟩
    refine ⟨?_, fun _ => ?_⟩
    · exact fun _ => root
    · have member := List.mem_of_getElem? stored
      simp only [state, List.mem_cons, List.mem_singleton] at member
      rcases member with rfl | rfl <;> simp
  have noCarrier : ¬ CarriesGraph state 1 := by
    rintro ⟨held, value, same, stored, bearing⟩
    have sameIndex : 1 = held := (UnionFind.initial_classes [0, 1] 1 held).mp same
    subst held
    change some (.unenumerated none [] : UVarValue Symbol) = some value at stored
    have valueSame := Option.some.inj stored
    cases valueSame
    exact bearing
  refine ⟨state, ⟨storage, live⟩, ?_, ?_, ?_, ?_, ?_, noCarrier, ?_, ?_⟩
  · simp [Canonical, state, references, ValidSuspended]
  · simp [ProperState, state, ProperValue]
  · intro uv node scs stored
    cases uv with
    | zero => simp [state] at stored
    | succ uv =>
        cases uv with
        | zero =>
            change some (.unenumerated none [] : UVarValue Symbol) = some (.unenumerated node scs) at stored
            have payloadSame := Option.some.inj stored
            cases payloadSame
            exact ⟨rfl, rfl⟩
        | succ uv => simp [state] at stored
  · refine ⟨assignment, ⟨UnionFind.initial_satisfies [0, 1] assignment, ?_⟩, by simp [guardsHold, state]⟩
    intro uv
    cases uv with
    | zero => simp [heap, state, slot, slotSatisfies, fill, assignment]
    | succ uv =>
        cases uv <;> simp [heap, state, slot, slotSatisfies, permits]
  · exact carries_self state (UnionFind.initial_total [0, 1]) 0
      (.enumerated (.node symbol [.hole 1])) rfl trivial
  · intro carried
    exact noCarrier (carried.1 0 (.node symbol [.hole 1]) rfl 1
      (.child symbol [.hole 1] (.hole 1) 1 (by simp) (.hole 1)))
  · intro heap marker fuel term pending after rendered
    cases fuel with
    | zero =>
        simp [Success, SourcePruningEnumerationRendering.render,
          SourcePruningEnumerationRendering.expandUVar, SourcePruningEnumerationRendering.expandFragment,
          getValue, representative, rawValue, UnionFind.findRoot, UnionFind.withInitialValues,
          state, failure, bind, pure, get, getThe, MonadStateOf.get, set,
          StateT.bind, StateT.pure, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure,
          ExceptT.bindCont, ExceptT.mk, ExceptT.run] at rendered
    | succ fuel =>
        cases fuel with
        | zero =>
            simp [Success, SourcePruningEnumerationRendering.render,
              SourcePruningEnumerationRendering.expandUVar, SourcePruningEnumerationRendering.expandFragment,
              getValue, representative, rawValue, UnionFind.findRoot, UnionFind.withInitialValues,
              state, failure, bind, pure, get, getThe, MonadStateOf.get, set,
              List.mapM_cons, List.mapM_nil, StateT.bind, StateT.pure, StateT.get, StateT.set,
              ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at rendered
        | succ fuel =>
            simp [Success, SourcePruningEnumerationRendering.render,
              SourcePruningEnumerationRendering.expandUVar, SourcePruningEnumerationRendering.expandFragment,
              getValue, representative, rawValue, UnionFind.findRoot, UnionFind.withInitialValues,
              state, failure, bind, pure, get, getThe, MonadStateOf.get, set,
              List.mapM_cons, List.mapM_nil, StateT.bind, StateT.pure, StateT.get, StateT.set,
              ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at rendered

end MicroCFTA.SourcePruningEnumerationFreeHole
