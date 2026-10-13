import MicroCFTA.EqualityNestedUnaryUnion

/-!
# The actual projected endpoint schedule on nested unary rows

This worker reads both projected unions before it edits any original
endpoint occurrence. It executes the current target merger and actual
nested intersections. Original occurrence indices remain explicit.
Ancestor reconstruction and required-path checks are separate boundaries.
-/
namespace MicroCFTA.EqualityNestedUnarySchedule
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct EqualityMergedTargetReadback
open EqualityNestedUnaryMeet EqualityNestedUnaryUnion

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

abbrev ValuesAt (symbols count : Nat) := Fin count → Value (Fin symbols) ConstraintKey
abbrev Physical (symbols left right : Nat) := ValuesAt symbols left × ValuesAt symbols right

/-- Each retained original index has an actual available canonical endpoint. -/
def Represents (parent leaf : Fin symbols) (state : State (Fin symbols) ConstraintKey)
    (rows : Fin count → Node initial) (values : ValuesAt symbols count) : Prop :=
  ∀ index, Available state (values index) ∧ Replayable (values index) ∧ NodeShape parent leaf (rows index) (values index)

/-- Complete endpoint records and their immutable row meanings persist under actual cache growth. -/
theorem represents_grows (parent leaf : Fin symbols) (before after : State (Fin symbols) ConstraintKey)
    (extension : Extension before after) (rows : Fin count → Node initial) (values : ValuesAt symbols count)
    (represented : Represents parent leaf before rows values) : Represents parent leaf after rows values :=
  fun index => ⟨extension.available (values index) (represented index).1, (represented index).2⟩

/-- List execution supplies the output related to a successful original index lookup. -/
theorem related_lookup (relation : Input → Output → Prop) (inputs : List Input) (outputs : List Output)
    (related : Language.All₂ relation inputs outputs) (index : Nat) (input : Input) (found : inputs[index]? = some input) :
    ∃ output, outputs[index]? = some output ∧ relation input output := by
  induction related generalizing index with
  | nil => simp at found
  | @cons first second rest remaining head tail ih =>
      cases index with
      | zero =>
          have same : first = input := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using found
          subst input
          exact ⟨second, rfl, head⟩
      | succ index => exact ih index found

/-- Map output decoding preserves each original finite index exactly. -/
theorem related_index (relation : Fin count → Output → Prop) (outputs : List Output)
    (related : Language.All₂ relation (List.finRange count) outputs) (fallback : Output) (index : Fin count) :
    relation index ((outputs[index.val]?).getD fallback) := by
  have found : (List.finRange count)[index.val]? = some index := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨by simpa only [List.length_finRange] using index.isLt, by simp⟩
  obtain ⟨output, stored, property⟩ := related_lookup relation _ _ related index.val index found
  simpa only [stored, Option.getD_some] using property

/-- Execute nested source intersection once at each original endpoint position. -/
noncomputable def edit (target : Value (Fin symbols) ConstraintKey) (values : ValuesAt symbols count) :
    Action (Fin symbols) ConstraintKey (ValuesAt symbols count) :=
  MergedColdMerge.bind (MergedColdMerge.map (fun index => meet (values index) target) (List.finRange count))
    (fun outputs => MergedColdMerge.pure (fun index => (outputs[index.val]?).getD .empty))

/-- Ordered endpoint execution implements the exact projected row edit at every original position. -/
theorem edit_complete (parent leaf : Fin symbols) (rows : Fin count → Node initial) (values : ValuesAt symbols count)
    (targetRows : Node initial) (target : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : Represents parent leaf state rows values)
    (targetValid : Available state target ∧ Replayable target ∧ NodeShape parent leaf targetRows target) :
    Complete (fun _ => edit target values) state (fun after result =>
      Represents parent leaf after (EqualityFixedProjectionInvariant.edit (Join initial) rows targetRows) result) := by
  let pre := fun (before : State (Fin symbols) ConstraintKey) (index : Fin count) =>
    Available before (values index) ∧ Available before target
  let post := fun (after : State (Fin symbols) ConstraintKey) (index : Fin count) (value : Value (Fin symbols) ConstraintKey) =>
    Available after value ∧ Replayable value ∧
      NodeShape parent leaf (EqualityFixedProjectionInvariant.narrow (Join initial) (rows index) targetRows) value
  have complete := MergedColdMergeSoundness.map_related (fun _ index => meet (values index) target) pre post
    (fun _ _ extension index valid => ⟨extension.available _ valid.1, extension.available _ valid.2⟩)
    (fun _ _ extension index value valid => ⟨extension.available _ valid.1, valid.2⟩)
    (List.finRange count) (fun index _ before facts prepared valid =>
      meet_complete parent leaf (rows index) targetRows (values index) target
        (represented index).2.2 targetValid.2.2 (represented index).2.1 targetValid.2.1
        before facts prepared valid.1 valid.2)
    state facts prepared (fun index _ => ⟨(represented index).1, targetValid.1⟩)
  apply bind_complete _ _ state _ _ complete
  intro outputs after extension related
  exact pure_complete _ after extension.facts extension.prepared _
    (fun index => related_index (post after) outputs related .empty index)

/-- Build and merge one snapshot projection with the source's ordered original occurrences. -/
noncomputable def target (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat)
    (values : ValuesAt symbols count) : Action (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  MergedColdMerge.bind (MergedColdMerge.work (makeUnion ((List.finRange count).map values)))
    (execute MergedSourceGrouping.groups clear top comparison)

/-- Snapshot target computation has exactly the union predicate of the original endpoint occurrences. -/
theorem target_exact (parent leaf : Fin symbols) (rows : Fin count → Node initial) (values : ValuesAt symbols count)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : Represents parent leaf state rows values)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    Complete (fun _ => target clear top comparison values) state (fun after result =>
      Available after result ∧ Replayable result ∧
        NodeShape parent leaf (EqualityFixedProjectionInvariant.project rows) result) := by
  let inputs := (List.finRange count).map (fun index => (rows index, values index))
  have valid : ∀ input ∈ inputs, Available state input.2 ∧ Replayable input.2 ∧ NodeShape parent leaf input.1 input.2 := by
    intro input member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact represented index
  have same : Project inputs = EqualityFixedProjectionInvariant.project rows := by
    funext row
    apply propext
    simp only [Project, inputs, List.mem_map, EqualityFixedProjectionInvariant.project]
    constructor
    · rintro ⟨_, ⟨index, _, rfl⟩, member⟩
      exact ⟨index, member⟩
    · rintro ⟨index, member⟩
      exact ⟨(rows index, values index), ⟨index, List.mem_finRange _, rfl⟩, member⟩
  have completed := target_complete parent leaf inputs small state facts prepared valid clear top comparison
  simpa only [inputs, List.map_map, Function.comp_def, same, target] using completed

/-- Both snapshot projections finish before the ordered left and right endpoint edits. -/
noncomputable def step (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat)
    (values : Physical symbols left right) : Action (Fin symbols) ConstraintKey (Physical symbols left right) :=
  MergedColdMerge.bind (target clear top comparison values.1) fun first =>
    MergedColdMerge.bind (target clear top comparison values.2) fun second =>
      MergedColdMerge.bind (edit second values.1) fun newLeft =>
        MergedColdMerge.bind (edit first values.2) fun newRight => MergedColdMerge.pure (newLeft, newRight)

/-- All actual projection, merge, intersection, and cache effects implement one reciprocal row-model pass. -/
theorem step_complete (parent leaf : Fin symbols) (rows : Projected initial left right) (values : Physical symbols left right)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : Represents parent leaf state rows.1 values.1 ∧ Represents parent leaf state rows.2 values.2)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    Complete (fun _ => step clear top comparison values) state (fun after result =>
      Represents parent leaf after (EqualityFixedProjectionTermination.step (Join initial) rows).1 result.1 ∧
      Represents parent leaf after (EqualityFixedProjectionTermination.step (Join initial) rows).2 result.2) := by
  apply bind_complete _ _ state _ _ (target_exact parent leaf rows.1 values.1 small state facts prepared represented.1 clear top comparison)
  intro first afterFirst firstExtension firstValid
  apply bind_complete _ _ afterFirst _ _ (target_exact parent leaf rows.2 values.2 small afterFirst firstExtension.facts firstExtension.prepared
    (represents_grows parent leaf state afterFirst firstExtension rows.2 values.2 represented.2) clear top comparison)
  intro second afterSecond secondExtension secondValid
  apply bind_complete _ _ afterSecond _ _ (edit_complete parent leaf rows.1 values.1 _ second afterSecond secondExtension.facts secondExtension.prepared
    (represents_grows parent leaf state afterSecond (firstExtension.trans secondExtension) rows.1 values.1 represented.1) secondValid)
  intro newLeft afterLeft leftExtension leftValid
  apply bind_complete _ _ afterLeft _ _ (edit_complete parent leaf rows.2 values.2 _ first afterLeft leftExtension.facts leftExtension.prepared
    (represents_grows parent leaf state afterLeft ((firstExtension.trans secondExtension).trans leftExtension) rows.2 values.2 represented.2)
    ⟨(secondExtension.trans leftExtension).available first firstValid.1, firstValid.2⟩)
  intro newRight afterRight rightExtension rightValid
  exact pure_complete _ afterRight rightExtension.facts rightExtension.prepared _
    ⟨represents_grows parent leaf afterLeft afterRight rightExtension _ newLeft leftValid, rightValid⟩

end MicroCFTA.EqualityNestedUnarySchedule
