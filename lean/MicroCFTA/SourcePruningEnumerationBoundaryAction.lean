import MicroCFTA.SourcePruningEnumerationAction
import MicroCFTA.SourcePruningOuterNarrowBoundary

/-!
# Identity actions at actual retained recursion boundaries

An actual boundary result retains the old native value and heap.
Its original encoded handle selects the identity enumeration action.
No later heap or handle identity is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationAction
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing Key : Type}
attribute [local instance] actionMonadList

/-- An actual completed boundary result retains its handle and selects the identity action. -/
theorem prepare_boundary_retained [DecidableEq (EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List Suspended)
    (oldValue : Value Symbol NativeGuard) (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (result : Value Symbol NativeGuard)
    (action : Option (EnumerateM Symbol EnumGuard Unit)) (after : InternedConstructorTemplates.State Symbol NativeGuard)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (available : Available heap oldValue) (closed : oldValue.free = [])
    (encoded : encodeNode oldValue = some oldHandle)
    (observed : prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
      scs oldValue heap = .done (result, action) after)
    (boundary : MergedOrdinaryHeight.recursiveBoundary result = true) :
    result = oldValue ∧ after = heap ∧ action = some (pure ()) := by
  have narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done result after := by
    unfold prepare at observed
    cases native : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
    | failed fault middle =>
        simp only [native] at observed
        cases observed
    | done produced middle =>
        simp only [native] at observed
        obtain ⟨pairSame, heapSame⟩ := MergedSourceComparison.Result.done.inj observed
        have resultSame : produced = result := congrArg Prod.fst pairSame
        subst result
        subst after
        rfl
  have kept := SourcePruningOuterNarrow.narrow_boundary_retained holeKey fits admits metadata nativeFuel uv
    oldValue heap result after ready available closed narrowed boundary
  have actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done oldValue heap := by simpa only [kept.1, kept.2] using narrowed
  have oldBoundary : MergedOrdinaryHeight.recursiveBoundary oldValue = true := by
    simpa only [kept.1] using boundary
  have unchanged : prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
      scs oldValue heap = .done (oldValue, some (pure () : EnumerateM Symbol EnumGuard Unit)) heap := by
    unfold prepare
    rw [actual]
    cases oldValue <;> simp_all only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true,
      ↓reduceIte]
  have same := MergedSourceComparison.Result.done.inj (observed.symm.trans unchanged)
  exact ⟨(Prod.mk.inj same.1).1, same.2, (Prod.mk.inj same.1).2⟩

end MicroCFTA.SourcePruningEnumerationAction
