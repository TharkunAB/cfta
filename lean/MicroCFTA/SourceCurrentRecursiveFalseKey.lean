import MicroCFTA.SourcePruningEnumerationRecursion

/-! The literal recursive false guard excludes its checked key at the returned root. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentRecursiveFalseKey
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint

/-- A successful recursive false check excludes the actual checked key. -/
theorem recursive_false_key_absent
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv handle : Nat) (scs : List Suspended) (value : Node)
    (before after : Core)
    (ready : EnumerationDriver.Ready uv before)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (observed : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      heap fuel uv handle scs before) = [.ok (false, after)]) :
    recursionKey handle scs ∉ after.recursionAncestry uv := by
  cases rootRead : UnionFind.findRoot fuel before.representatives uv with
  | none =>
      simp [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
        EnumerationState.representative, rootRead, EnumerationState.failure,
          get, pure, bind, getThe, MonadStateOf.get,
          StateT.bind, StateT.get, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
          ExceptT.mk, ExceptT.run] at observed
  | some found =>
      let resolved : Core := {before with representatives := found.forest}
      have represented : ExceptT.run (representative fuel uv before) =
          [.ok (found.representative, resolved)] := by
        simp [EnumerationState.representative, rootRead, resolved, get, set, pure, bind, getThe,
          MonadStateOf.get, StateT.bind, StateT.pure, StateT.get, StateT.set,
          ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run]
      have rootFacts := EnumerationDriver.representative_root fuel uv found.representative
        before resolved ready.safe ready.inside ready.root (by
          change Except.ok (found.representative, resolved) ∈
            ExceptT.run (representative fuel uv before)
          rw [represented]
          simp)
      have sameRoot : found.representative = uv := rootFacts.1
      by_cases member : recursionKey handle scs ∈ before.recursionAncestry found.representative
      · simp [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
          EnumerationState.representative, rootRead, member, setValue, get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          pure, bind, getThe, MonadStateOf.get, StateT.bind,
          StateT.pure, StateT.get, StateT.set, ExceptT.bind, ExceptT.bindCont,
          ExceptT.pure, ExceptT.mk, ExceptT.run] at observed
      · have afterSame : resolved = after := by
          simpa [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
            EnumerationState.representative, rootRead, member, resolved, get, set, pure, bind, getThe,
          MonadStateOf.get, StateT.bind, StateT.pure, StateT.get, StateT.set,
          ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, ExceptT.run] using observed
        rw [← afterSame]
        simpa only [resolved, sameRoot] using member

end MicroCFTA.SourceCurrentRecursiveFalseKey
