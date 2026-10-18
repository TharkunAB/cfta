import MicroCFTA.InternedFreshOrdinaryDepthHeap
import MicroCFTA.InternedEdgeResidency

/-!
# Physical ordinary rows after smart Mu cleanup

A physical row excludes both the retained Mu and bare-self empty return.
The produced probe-depth invariant then identifies the unused-local branch.
Arbitrary unrelated body and probe fields need not satisfy that invariant.
The result does not assume a restriction on nested binder syntax.
-/
namespace MicroCFTA.SourceCurrentNativeOrdinaryMuFinish
open Cache InternedConstructorTemplates
open InternedNestedConstruction (finish)
open InternedFreshOrdinaryDepthHeap (Correct usesLocal decodedDepth)
open InternedEdgeResidency (nodeEdges)

/-- A physical finished row selects the unused body and its exact original row occurrence. -/
theorem selected (entry : Interned InternedBinderProtocol.NodeKey)
    (storedBody depth ordinary : Value Symbol Guard)
    (correct : Correct entry storedBody depth ordinary)
    (result : Value Symbol Guard)
    (finished : finish true (.mu entry storedBody depth ordinary) = result)
    (index : Nat) (row : EdgeValue Symbol Guard)
    (present : (nodeEdges result)[index]? = some row) :
    usesLocal depth ordinary = false ∧ result = storedBody ∧
      InternedBinderProtocol.Reference.interned entry.identity ∉ storedBody.free ∧
      (nodeEdges storedBody)[index]? = some row := by
  have bodyOnly : InternedBinderProtocol.Reference.interned entry.identity ∉ storedBody.free ∧
      result = storedBody := by
    have actual := finished
    simp only [finish, Bool.true_eq, ite_true, cleanup] at actual
    split at actual
    · exact ⟨by assumption, actual.symm⟩
    · split at actual
      · rw [← actual] at present
        simp only [nodeEdges, List.getElem?_nil] at present
        cases present
      · rw [← actual] at present
        simp only [nodeEdges, List.getElem?_nil] at present
        cases present
  have bodyDepth : storedBody.depth = depth.depth := by
    simpa only [finish, Value.depth, decodedDepth, Bool.not_false, Bool.true_or,
      Bool.false_eq_true, ite_true, ite_false, Nat.add_right_cancel_iff] using (correct false).1
  have smart := (correct true).1
  rw [finished, bodyOnly.2, bodyDepth] at smart
  have unused : usesLocal depth ordinary = false := by
    cases found : usesLocal depth ordinary <;> simp [decodedDepth, found] at smart ⊢
  exact ⟨unused, bodyOnly.2, bodyOnly.1, by simpa only [bodyOnly.2] using present⟩

end MicroCFTA.SourceCurrentNativeOrdinaryMuFinish
