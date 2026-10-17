import MicroCFTA.InternedStoredEncodingMass
import MicroCFTA.SourceRecursiveIntersectionSourceProfile
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.EncodingMassKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredShallowCompletion (BinderFree)
local notation "Mass" => InternedValueMass.value
variable {Symbol Guard : Type}

/-- Initial successful source payload sizes bound later local encoding allocations under the caller's SizeOf instances. -/
theorem initial_payload_bound [SizeOf Symbol] [SizeOf Guard] [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (facts : Facts source) (input : Value Symbol Guard)
    (available : Available source input) (identity : Nat)
    (recorded : SourcePreparedSharedRows.reference input = some identity)
    (environment : Environment Symbol Guard) (current : State Symbol Guard) :
    let limit := SourceRecursiveIntersectionSourceProfile.nodeSize source
    Mass input ≤ limit ∧
      (execute input environment current).state.nodes.next + 2 ≤ current.nodes.next + 2 * 3 ^ limit ∧
      (execute input environment current).state.edges.next + 2 ≤ current.edges.next + 2 * 3 ^ limit ∧
      (unfold input current).state.nodes.next + 2 ≤ current.nodes.next + 2 * 3 ^ limit ∧
      (unfold input current).state.edges.next + 2 ≤ current.edges.next + 2 * 3 ^ limit := by
  have small := Nat.le_trans (InternedValueMass.value_le_sizeOf input)
    (SourceRecursiveIntersectionSourceProfile.available_size source facts input available identity recorded)
  have growth := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < 3) small)
  have first := InternedStoredEncodingMass.execute_bound input environment current
  have last := InternedStoredEncodingMass.unfold_bound input current
  exact ⟨small, by omega, by omega, by omega, by omega⟩

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0,
    .binder false (.node [.mk 1 true [.var 0, .var 1, .var 2]])]])

private theorem initial :
    ∃ input source, InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source ∧
      Available source input ∧
      InternedFreshOrdinaryContext.Context source [.reference (.intersection 3 5)] ∧
      InternedFreshOrdinaryDepthHeap.Heap source ∧ InternedRecordCoherence.Covered [] source := by
  have literal : Available (empty : State Nat Bool) (.reference (.intersection 3 5)) :=
    reference_available empty _ (by
      intro identity member
      have impossible : Reference.interned identity = Reference.intersection 3 5 := List.mem_singleton.mp member
      cases impossible)
  have context := InternedFreshOrdinaryContext.empty_context.local (.intersection 3 5) literal
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete expression
    [.intersection 3 5] empty context InternedFreshOrdinaryDepthHeap.empty_heap InternedRecordCoherence.empty_correct.2
  change InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source at built
  have checked := InternedFreshOrdinaryFacts.build_verified expression _ empty empty_facts context.inputs
  have contexts : InternedFreshOrdinaryContext.Context
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty).state
      [.reference (.intersection 3 5)] := context.build expression
  have depths : InternedFreshOrdinaryDepthHeap.Heap
      (InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty).state :=
    (InternedRecordDepthExecution.build_depth expression _ empty context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  refine ⟨input, source, built, checked.result input source built,
    by simpa only [built, Outcome.state] using contexts,
    by simpa only [built, Outcome.state] using depths, ?_⟩
  exact InternedFreshOrdinaryCoverage.build_covered expression _ empty empty_valid InternedRecordCoherence.empty_correct.2 input source built

private theorem observed : match InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty with
    | .pending .. => False
    | .done input _ => Reference.intersection 3 5 ∈ input.free ∧
        ¬ BinderFree (encode (leaves input) [] input) ∧
        (match input with | .mu _ body _ _ => ¬ BinderFree (encode (leaves body) [] body) | _ => False) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 200000000 in cbv
  simp
  exact .head _


/-- Own construction and unfolding of an open nested Mu derive actual mass-based counter bounds. -/
theorem constructed_nested_unfold :
    ∃ input source result after,
      InternedFreshOrdinaryConstruction.build expression [.reference (.intersection 3 5)] empty = .done input source ∧
      Reference.intersection 3 5 ∈ input.free ∧
      ¬ InternedStoredClosedMuCompletion.PreparedWithoutMu input ∧
      unfold input source = .done result after ∧ Available after result ∧
      after.nodes.next + 2 ≤ source.nodes.next + 2 * 3 ^ Mass input ∧
      after.edges.next + 2 ≤ source.edges.next + 2 * 3 ^ Mass input := by
  obtain ⟨input, source, built, available, context, depth, covered⟩ := initial
  have shape := observed
  rw [built] at shape
  dsimp only at shape
  have nontrivial : ¬ InternedStoredClosedMuCompletion.PreparedWithoutMu input := by
    intro prepared
    exact shape.2.1 (InternedStoredClosedMuCompletion.encode_withoutMu (leaves input) [] input prepared)
  obtain ⟨result, after, done, _context, _depth, _covered, output, _growth, _history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded input source context available depth covered
  have counts := InternedStoredEncodingMass.unfold_bound input source
  exact ⟨input, source, result, after, built, shape.1, nontrivial, done, output,
    by simpa only [done, Outcome.state] using counts⟩

end MicroCFTA.EncodingMassKernels

#print axioms MicroCFTA.EncodingMassKernels.initial_payload_bound
#check @MicroCFTA.EncodingMassKernels.initial_payload_bound
#print axioms MicroCFTA.EncodingMassKernels.constructed_nested_unfold
#check @MicroCFTA.EncodingMassKernels.constructed_nested_unfold
