import MicroCFTA.SourcePruningEnumerationSelectedStepCompletion
import MicroCFTA.SourcePruningEnumerationCarrierFrame

/-!
# Graph provenance through actual selected-prefix operations

A representative read retains every old carrier.
A pending write stores an actual graph handle.
The observers include retained parked caches.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedPrefixCarriers
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationCompressionFrame
open EnumerationDependencies EnumerationCarriers EnumerationGraphReferences
open SourcePruningEnumerationNodes
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

private theorem pending_write_carriers {EnumGuard : Type}
    (uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (observed : Success (setValue uv (.unenumerated (some handle) scs)) before () after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after := by
  have origin := setValue_origin uv (.unenumerated (some handle) scs) before after
    (by intro fragment; intro impossible; cases impossible) observed
  obtain rfl := (EnumerationDriver.modify_success _ before after).mp observed
  have preserved := set_graph_carriers before uv (.unenumerated (some handle) scs) trivial
  exact ⟨total, preserved, references_transport _ _ references preserved origin rfl⟩

/-- Every successful recursion check retains carriers and stored references. -/
theorem checkRepeated_carriers {EnumGuard NativeGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (repeated : Bool)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before repeated after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after repeated impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        have frame := representative_frame fuel uv root before resolved total resolution
        obtain ⟨current, reading, read, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, readingSame⟩ := (EnumerationDriver.get_success resolved reading current).mp read
        subst current
        subst reading
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry root
        · rw [ite_eq_left seen] at continued
          obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          have writtenFacts := pending_write_carriers root handle [] resolved written
            (frame.total total) (frame.references references) writing
          obtain ⟨_same, afterSame⟩ := (success_pure true repeated written after).mp finished
          subst after
          exact ⟨writtenFacts.1, frame.carriers.trans writtenFacts.2.1, writtenFacts.2.2⟩
        · rw [ite_eq_right seen] at continued
          obtain ⟨_same, afterSame⟩ := (success_pure false repeated resolved after).mp continued
          subst after
          exact ⟨frame.total total, frame.carriers, frame.references references⟩
      · have pureObserved : Success (pure false) before repeated after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using observed
        obtain ⟨_same, afterSame⟩ := (success_pure false repeated before after).mp pureObserved
        subst after
        exact ⟨total, .refl _, references⟩

/-- A successful prepared action retains every old carrier and stored reference. -/
theorem prepared_nonempty_carriers {Typing Key : Type}
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol Constraint → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : InternedConstructorTemplates.Value Symbol Constraint)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (checked after : EnumerationState.State Symbol Constraint)
    (total : UnionFind.Total checked.representatives) (references : ReferencesCarry checked)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers checked after ∧ ReferencesCarry after := by
  have actual := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
    nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap
    narrowed nonempty encoded
  rw [prepared] at actual
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actual).1).2
  rw [actionSame] at observed
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at observed
    obtain ⟨_same, afterSame⟩ := (success_pure () () checked after).mp observed
    subst after
    exact ⟨total, .refl _, references⟩
  · rw [ite_eq_right same] at observed
    obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ _ _ _).mp observed
    have frame := representative_frame representativeFuel uv selected checked resolved total reading
    have written := pending_write_carriers selected newHandle scs resolved after
      (frame.total total) (frame.references references) writing
    exact ⟨written.1, frame.carriers.trans written.2.1, written.2.2⟩

end MicroCFTA.SourcePruningEnumerationSelectedPrefixCarriers
