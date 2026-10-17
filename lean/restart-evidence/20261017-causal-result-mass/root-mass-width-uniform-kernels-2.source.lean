import MicroCFTA.InternedFreshOrdinaryUniformMass
import MicroCFTA.InternedStoredEncodingMass
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.RootMassWidthUniformKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
local notation "Mass" => InternedValueMass.value
local notation "Stored" => InternedValueMassHeap.Stored
local notation "Width" => InternedStoredEncodingWidth.Width
local notation "evolve" => InternedFreshOrdinaryUniformMass.evolve
local notation "nodeBudget" => InternedFreshOrdinaryAllocationBudget.nodeBudget
local notation "edgeBudget" => InternedFreshOrdinaryAllocationBudget.edgeBudget
variable {Symbol Guard : Type}

/-- An initial decoded cache constructs its own full source return and numeric payload store. -/
theorem constructed_uniform [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (source : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context source environment)
    (depth : InternedFreshOrdinaryDepthHeap.Heap source) (covered : InternedRecordCoherence.Covered [] source)
    (width : Nat) (fits : Width width expression) :
    let bound := evolve width (nodeBudget expression + edgeBudget expression) (InternedValueMassHeap.initialBound source)
    ∃ value after,
      InternedFreshOrdinaryConstruction.build expression environment source = .done value after ∧
      InternedFreshOrdinaryContext.Context after environment ∧
      InternedFreshOrdinaryDepthHeap.Heap after ∧ InternedRecordCoherence.Covered [] after ∧
      Available after value ∧ Stored bound after ∧ Mass value ≤ bound ∧ Width bound (encode (leaves value) [] value) := by
  dsimp only
  let initial := InternedValueMassHeap.initialBound source
  have stored := InternedValueMassHeap.initial source context.normal.facts
  have inputs : ∀ value ∈ environment, Mass value ≤ initial :=
    fun value member => InternedValueMassHeap.available source stored value (context.inputs value member)
  have mass := InternedFreshOrdinaryResultMass.build_bound expression environment source initial stored inputs
  have numeric := InternedFreshOrdinaryUniformMass.transform_bound width expression initial fits
  obtain ⟨value, after, done⟩ := InternedRecordDepthCompletion.source_complete expression environment source context depth covered
  have contexts : InternedFreshOrdinaryContext.Context
      (InternedFreshOrdinaryConstruction.build expression environment source).state environment := context.build expression
  have depths : InternedFreshOrdinaryDepthHeap.Heap
      (InternedFreshOrdinaryConstruction.build expression environment source).state :=
    (InternedRecordDepthExecution.build_depth expression environment source context depth).heap
  have actualStored : Stored (InternedFreshOrdinaryResultMass.transform expression initial) after := by
    simpa only [done, Outcome.state] using mass.1
  have bounded := Nat.le_trans (mass.2 value after done) numeric
  refine ⟨value, after, done,
    by simpa only [done, Outcome.state] using contexts,
    by simpa only [done, Outcome.state] using depths,
    InternedFreshOrdinaryCoverage.build_covered expression environment source context.normal.facts.coherent.valid covered value after done,
    (InternedFreshOrdinaryFacts.build_verified expression environment source context.normal.facts context.inputs).result value after done,
    actualStored.mono numeric, bounded, ?_⟩
  exact InternedStoredEncodingWidth.encode_width (leaves value) [] value _ bounded

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0,
    .binder false (.node [.mk 1 true [.var 0, .var 1, .var 2]])]])

private theorem width : Width 3 expression := by
  simp [expression, InternedStoredEncodingWidth.Width, InternedStoredEncodingWidth.Many,
    InternedStoredEncodingWidth.Rows]

private theorem observed : match InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty with
    | .pending .. => False
    | .done value _ => Reference.intersection 3 5 ∈ value.free ∧
        ¬ InternedStoredShallowCompletion.BinderFree (encode (leaves value) [] value) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 200000000 in cbv
  simp
  exact .head _

/-- A full open nested Mu constructs its own result-fed reconstruction under initial-only numeric mass bounds. -/
theorem nested_result_fed :
    let firstBound := evolve 3 (nodeBudget expression + edgeBudget expression)
      (InternedValueMassHeap.initialBound (empty : State Nat Bool))
    let finalBound := evolve firstBound (4 * 3 ^ firstBound) firstBound
    ∃ value middle result after,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done value middle ∧
      Reference.intersection 3 5 ∈ value.free ∧ ¬ InternedStoredClosedMuCompletion.PreparedWithoutMu value ∧
      Stored firstBound middle ∧ Width firstBound (encode (leaves value) [] value) ∧
      execute value (fun _ => none) middle = .done result after ∧ Available after result ∧
      Stored finalBound after ∧ Mass result ≤ finalBound := by
  dsimp only
  have literal : Available (empty : State Nat Bool) (.reference (.intersection 3 5)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection 3 5 := List.mem_singleton.mp member
      cases impossible)
  have context := InternedFreshOrdinaryContext.empty_context.local (.intersection 3 5) literal
  obtain ⟨value, middle, built, middleContext, middleDepth, middleCovered, available, stored, bounded, fits⟩ :=
    constructed_uniform expression [.reference (.intersection 3 5)] empty context
      InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2 3 width
  have shape := observed
  rw [built] at shape
  dsimp only at shape
  have noPreparation : ¬ InternedStoredClosedMuCompletion.PreparedWithoutMu value := by
    intro prepared
    exact shape.2 (InternedStoredClosedMuCompletion.encode_withoutMu (leaves value) [] value prepared)
  have replacements : InternedStoredSubstitution.Replacements middle (fun _ => none) := by
    intro name replacement found
    cases found
  obtain ⟨result, after, done, _context, _depth, _covered, output, _growth, _history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.execute_complete_decoded value (fun _ => none) middle
      middleContext available replacements middleDepth middleCovered
  let firstBound := evolve 3 (nodeBudget expression + edgeBudget expression)
    (InternedValueMassHeap.initialBound (empty : State Nat Bool))
  let plan := encode (leaves value) [] value
  have inputs := InternedStoredSubstitution.inputs_available value (fun _ => none) middle available replacements
  have inputsMass : ∀ capture ∈ (leaves value).map (input (fun _ => none)), Mass capture ≤ firstBound :=
    fun capture member => InternedValueMassHeap.available middle stored capture (inputs capture member)
  have actual := InternedFreshOrdinaryResultMass.build_bound plan _ middle firstBound stored inputsMass
  have numeric := InternedFreshOrdinaryUniformMass.transform_bound firstBound plan firstBound fits
  have encodeBudget := InternedStoredEncodingMass.encode_bound (leaves value) [] value
  have potential := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < 3) bounded)
  change 2 * 3 ^ Mass value ≤ 2 * 3 ^ firstBound at potential
  have steps : nodeBudget plan + edgeBudget plan ≤ 4 * 3 ^ firstBound := by
    dsimp only [plan]
    omega
  have schedule := InternedFreshOrdinaryUniformMass.evolve_count_mono firstBound steps firstBound
  have transfer := Nat.le_trans numeric schedule
  have completed : InternedFreshOrdinaryConstruction.build plan
      ((leaves value).map (input (fun _ => none))) middle = .done result after := done
  have finalStored : Stored (InternedFreshOrdinaryResultMass.transform plan firstBound) after := by
    simpa only [completed, Outcome.state] using actual.1
  have finalMass := Nat.le_trans (actual.2 result after done) transfer
  exact ⟨value, middle, result, after, built, shape.1, noPreparation, stored, fits,
    done, output, finalStored.mono transfer, finalMass⟩

end MicroCFTA.RootMassWidthUniformKernels

#print axioms MicroCFTA.RootMassWidthUniformKernels.constructed_uniform
#check @MicroCFTA.RootMassWidthUniformKernels.constructed_uniform
#print axioms MicroCFTA.RootMassWidthUniformKernels.nested_result_fed
#check @MicroCFTA.RootMassWidthUniformKernels.nested_result_fed
