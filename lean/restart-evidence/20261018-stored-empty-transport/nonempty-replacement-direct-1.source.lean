import MicroCFTA.SourceCurrentStoredEmptyCongruence
import MicroCFTA.SourceCurrentStoredEmptyInterpreter
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.InternedStoredCostRetention

/-!
# Physical Empty under nonempty stored replacements

Positive original occurrence costs prevent a live stored plan from
becoming Empty under identity replacement. Empty congruence extends this
fact to arbitrary nonempty replacements on the original free names.
The proof retains the full stored plan and includes open nested Mu values.
-/
namespace MicroCFTA.SourceCurrentStoredNonemptyReplacement
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedRecordDepthShape (shape)
open InternedFreeOccurrenceRank (costs)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (Reference NodeKey)

private theorem identity_inputs (context : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (available : InternedNestedProvenance.Values state context) :
    InternedStoredCostInputs.Inputs context [] (context.map shape) (context.map costs)
      (fun name => [(name,0)]) := by
  refine ⟨InternedRecordDepthShape.input_coherent context,?_,?_,?_,?_⟩
  · intro index name count member
    cases found : context[index]? with
    | none => simp [List.getElem?_map,found] at member
    | some value =>
        have present := available value (List.mem_of_getElem? found)
        have selected : (name,count) ∈ costs value := by
          simpa only [List.getElem?_map,found,Option.map_some,Option.getD_some] using member
        have named := (InternedFreeOccurrenceRank.costs_free value state normal.facts.coherent present name).mp
          ⟨count,selected⟩
        simpa only [List.getElem?_map,found,Option.map_some,Option.getD_some] using
          (InternedRecordDepthShape.shape_free value state normal.facts.coherent present name).mpr named
  · intro value member _
    have found := InternedStoredSubstitutionScope.slot_lookup context value state normal.facts.coherent available member
    simp only [List.length_nil,Nat.zero_add,List.getElem?_map,found,Option.map_some,Option.getD_some]
    exact (InternedRecordDepthShape.observed value state normal (available value member)).1.symm
  · intro name member
    have found := InternedStoredSubstitutionScope.slot_lookup context (.reference name) state
      normal.facts.coherent available member
    simp [encode,Value.free,InternedOccurrenceCostSemantics.evaluate,List.getElem?_map,found,costs]
  · intro name
    simp

private theorem identity_test (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (available : Available state value) :
    SourceCurrentStoredEmptyInterpreter.test value (fun _ => none) = (value.referenceOf == .empty) := by
  let context := leaves value
  have inputs := identity_inputs context state normal (InternedStoredSubstitution.leaves_available value state available)
  have retained := InternedStoredCostRetention.encode_retains context [] value state normal available
    (fun _ member => member) (context.map shape) (context.map costs) (fun name => [(name,0)]) inputs
  have projected := InternedDepthSemanticProjections.evaluate_profile (encode context [] value)
    (context.map shape) (InternedRecordDepthShape.input_coherent context)
  rw [InternedRecordDepthShape.input_profiles] at projected
  have resolved : context.map (fun leaf => InternedRootProfile.profile (input (fun _ => none) leaf)) =
      context.map InternedRootProfile.profile := by
    apply List.map_congr_left
    intro leaf _
    cases leaf <;> rfl
  have pureTest : SourceCurrentStoredEmptyInterpreter.test value (fun _ => none) =
      (InternedDepthSemantics.evaluate (encode context [] value) (context.map shape)).isEmpty := by
    unfold SourceCurrentStoredEmptyInterpreter.test
    change InternedProfileSemantics.isEmpty (InternedProfileSemantics.evaluate (encode context [] value)
      (context.map (fun leaf => InternedRootProfile.profile (input (fun _ => none) leaf)))) = _
    rw [resolved,← projected,InternedDepthSemanticProjections.profile_empty]
  by_cases empty : value.referenceOf = .empty
  · have literal : value = .empty := by cases value <;> simp_all [Value.referenceOf]
    subst value
    rw [SourceCurrentStoredEmptyInterpreter.closed _ _ rfl]
    rfl
  · rw [pureTest,retained.2 empty]
    exact (beq_eq_false_iff_ne.mpr empty).symm

/-- Nonempty replacements on original free names preserve the actual physical Empty test. -/
theorem execute_nonempty [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before) (available : Available before value)
    (replacements : Replacements before environment) (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute value environment before = .done result after)
    (nonempty : ∀ name ∈ value.free, ((environment name).getD (.reference name)).referenceOf ≠ .empty) :
    (result.referenceOf == .empty) = (value.referenceOf == .empty) := by
  have identityReplacements : Replacements before (fun _ => none) := by intro name replacement found; cases found
  obtain ⟨identity,final,done,_,_,_⟩ := SourceCurrentStoredReconstruction.execute value (fun _ => none)
    before ready available identityReplacements
  have same := SourceCurrentStoredEmptyCongruence.execute_same value environment (fun _ => none) before before
    ready ready available available replacements identityReplacements result after identity final actual done (by
      intro name member
      simpa only [Option.getD_none,Value.referenceOf] using beq_eq_false_iff_ne.mpr (nonempty name member))
  exact same.trans ((SourceCurrentStoredEmptyInterpreter.execute_test value (fun _ => none) before ready available
    identityReplacements identity final done).trans (identity_test value before ready.semantic.1.normal available))

end MicroCFTA.SourceCurrentStoredNonemptyReplacement
