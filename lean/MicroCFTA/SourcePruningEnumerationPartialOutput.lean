import MicroCFTA.SourcePruningPartialRenderingSemantics
import MicroCFTA.EnumerationPartialCompletion
import MicroCFTA.EnumerationPartialExact
import MicroCFTA.EnumerationPartialRoot
import MicroCFTA.SourcePruningEnumerationNodes
import MicroCFTA.MergedOrdinaryHeight

/-!
# Actual native partial output with original assignment completions

The existing partial observer needs only a recursive-boundary tag.
The private adapter obtains that tag from actual native handle lookup.
Its other graph fields have no language or intersection interpretation.
Operational bounds and complete returned states precede all model observers.
Pending holes and recursive truncation do not require Discharged storage.
-/
namespace MicroCFTA.SourcePruningEnumerationPartialOutput
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationCompressionFrame EnumerationOrder EnumerationUntil
open EnumerationExecution EnumerationObservations SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

attribute [local instance] EnumerationObservations.partialTransportMonadList
  EnumerationObservations.partialTransportLawfulMonadList

/-- Supply only the native boundary tag to the existing partial observer. -/
private def boundaryView (heap : InternedConstructorTemplates.State Symbol NativeGuard) :
    Graph Symbol EnumGuard where
  node handle :=
    match lookupNode heap handle with
    | none => .unresolved handle
    | some value =>
        if MergedOrdinaryHeight.recursiveBoundary value then .recursive handle
        else .unresolved handle
  intersect left _right := left

/-- Use actual native boundary lookup in the existing partial-rendering worker. -/
def expandPartial (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (fragment : Fragment Symbol) :
    EnumerateM Symbol EnumGuard (Term (PartialSymbol Symbol)) :=
  EnumerationState.expandPartial (boundaryView heap) fuel fragment

/-- Read the actual root fragment and then render it at the same finite bound. -/
def rootPartial (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat) :
    EnumerateM Symbol EnumGuard (Term (PartialSymbol Symbol)) :=
  rootFragment fuel >>= expandPartial heap fuel

/-- Native partial observation truncates only decoded empty-bucket recursive boundaries. -/
theorem expandPartial_hole
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat) :
    expandPartial (EnumGuard := EnumGuard) heap (fuel + 1) (.hole uv) = (do
      match ← getValue (fuel + 1) uv with
      | .enumerated fragment => expandPartial heap fuel fragment
      | .unenumerated (some handle) [] =>
          match lookupNode heap handle with
          | none => pure (.node (.hole uv) [])
          | some value =>
              if MergedOrdinaryHeight.recursiveBoundary value then pure (.node .truncated [])
              else pure (.node (.hole uv) [])
      | _ => pure (.node (.hole uv) [])) := by
  simp only [expandPartial, EnumerationState.expandPartial]
  congr 1
  funext slot
  cases slot with
  | eliminated | enumerated _ => rfl
  | unenumerated node scs =>
      cases node with
      | none => rfl
      | some handle =>
          cases scs with
          | cons _ _ => rfl
          | nil =>
              dsimp only [boundaryView]
              cases decoded : lookupNode heap handle with
              | none => rfl
              | some value =>
                  cases boundary : MergedOrdinaryHeight.recursiveBoundary value <;> simp [boundary]

/-- One actual native partial result represents every model of the original fragment. -/
theorem expandPartial_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (level : Nat → Nat) (frontier : Nat) (fragment : Fragment Symbol)
    (before : State Symbol EnumGuard) (safe : Safe before)
    (stratified : Stratified before level frontier) (allocated : FragmentBound before.counter fragment) :
    ∃ bound observedTerm after,
      (∀ extra,
        Success (expandPartial heap (bound + extra) fragment) before observedTerm after ∧
        ExceptT.run (expandPartial heap (bound + extra) fragment before) = [.ok (observedTerm, after)]) ∧
      RenderStable before after ∧ Frame before after ∧ Stratified after level frontier ∧
      ∀ (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
        (assignment : Nat → Term Symbol),
        Satisfies language meaning assignment before →
          Satisfies language meaning assignment after ∧
          SourcePruningPartialMatch.Completes assignment observedTerm (fill assignment fragment) := by
  obtain ⟨bound, observedTerm, after, actual, stable, frame, ordered⟩ :=
    EnumerationPartialCompletion.expandPartial_complete (boundaryView heap) level frontier fragment before
      safe stratified allocated
  refine ⟨bound, observedTerm, after, ?_, stable, frame, ordered, ?_⟩
  · intro extra
    have raised := EnumerationObservations.expandPartial_moreFuel (boundaryView heap) bound extra
      fragment before observedTerm after actual
    exact ⟨raised, EnumerationPartialExact.expandPartial_exact (boundaryView heap) (bound + extra)
      fragment before after observedTerm raised⟩
  · intro language meaning assignment satisfied
    exact ⟨(SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning
      assignment before after frame).mpr satisfied,
      SourcePruningPartialRenderingSemantics.expandPartial_completes (boundaryView heap)
        language meaning assignment bound fragment before after observedTerm safe.1.total satisfied actual⟩

private theorem root_read_exact (fuel : Nat) (before after : State Symbol EnumGuard)
    (fragment : Fragment Symbol) (actual : Success (rootFragment fuel) before fragment after) :
    ExceptT.run (rootFragment fuel before) = [.ok (fragment, after)] := by
  obtain ⟨value, reading, projected⟩ := (rootFragment_success fuel before after fragment).mp actual
  unfold rootFragment
  rw [bind_single _ _ _ _ _ (EnumerationPartialExact.getValue_exact (fuel + 1) 0 before after value reading)]
  cases value <;> cases projected <;> rfl

private theorem root_exact
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel : Nat)
    (before after : State Symbol EnumGuard) (observedTerm : Term (PartialSymbol Symbol))
    (actual : Success (rootPartial heap fuel) before observedTerm after) :
    ExceptT.run (rootPartial heap fuel before) = [.ok (observedTerm, after)] := by
  unfold rootPartial at actual ⊢
  obtain ⟨fragment, middle, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp actual
  rw [bind_single _ _ _ _ _ (root_read_exact fuel before middle fragment rootRead)]
  exact EnumerationPartialExact.expandPartial_exact (boundaryView heap) fuel fragment middle after observedTerm rendered

private theorem root_completes
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel : Nat) (before after : State Symbol EnumGuard)
    (observedTerm : Term (PartialSymbol Symbol)) (total : UnionFind.Total before.representatives)
    (satisfied : Satisfies language meaning assignment before)
    (actual : Success (rootPartial heap fuel) before observedTerm after) :
    SourcePruningPartialMatch.Completes assignment observedTerm (assignment 0) := by
  obtain ⟨fragment, middle, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp actual
  have frame := rootFragment_frame fuel before middle fragment total rootRead
  have middleModel := (SourcePruningEnumerationNativeLanguage.satisfies_frame
    language meaning assignment before middle frame).mpr satisfied
  have completed := SourcePruningPartialRenderingSemantics.expandPartial_completes (boundaryView heap)
    language meaning assignment fuel fragment middle after observedTerm (frame.total total) middleModel rendered
  have rootFilled : fill assignment fragment = assignment 0 := by
    obtain ⟨value, reading, projected⟩ := (rootFragment_success fuel before middle fragment).mp rootRead
    obtain ⟨_readFrame, root, _size, path, _afterPath, stored⟩ :=
      getValue_frame (fuel + 1) 0 before middle value total reading
    cases value with
    | eliminated | unenumerated _ _ => simp only [projected, fill]
    | enumerated storedFragment =>
        rw [projected]
        have rootEquation : fill assignment storedFragment = assignment root := by
          simpa only [EnumerationCorrectness.heap, stored, Option.getD_some, slot, slotSatisfies]
            using satisfied.1.2 root
        exact rootEquation.trans (satisfied.1.1 0 root (UnionFind.sameClass_root path)).symm
  rw [rootFilled] at completed
  exact completed

/-- One native partial root result and its full endpoint precede all original model observers. -/
theorem rootPartial_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (level : Nat → Nat) (frontier : Nat) (before : State Symbol EnumGuard)
    (safe : Safe before) (stratified : Stratified before level frontier) (inside : 0 < before.counter) :
    ∃ bound observedTerm after,
      (∀ extra,
        Success (rootPartial heap (bound + extra)) before observedTerm after ∧
        ExceptT.run (rootPartial heap (bound + extra) before) = [.ok (observedTerm, after)]) ∧
      RenderStable before after ∧ Frame before after ∧ Stratified after level frontier ∧
      ∀ (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
        (assignment : Nat → Term Symbol),
        Satisfies language meaning assignment before →
          Satisfies language meaning assignment after ∧
          SourcePruningPartialMatch.Completes assignment observedTerm (assignment 0) := by
  obtain ⟨readFuel, root, value, middle, reading, readStable, stored, _size, _path⟩ :=
    EnumerationPartialCompletion.getValue_complete before safe 0 inside
  let fragment : Fragment Symbol := match value with | .enumerated stored => stored | _ => .hole 0
  have rootRead : Success (rootFragment readFuel) before fragment middle :=
    (rootFragment_success readFuel before middle fragment).mpr
      ⟨value, getValue_moreFuel readFuel 1 0 before value middle reading,
        by cases value <;> simp [fragment]⟩
  have allocated : FragmentBound middle.counter fragment := by
    cases value with
    | enumerated storedFragment =>
        change FragmentBound middle.counter storedFragment
        rw [readStable.counter]
        exact safe.1.values _ (List.mem_of_getElem? stored)
    | eliminated | unenumerated _ _ =>
        change 0 < middle.counter
        rw [readStable.counter]
        exact inside
  obtain ⟨renderFuel, observedTerm, after, rendered, renderStable, _renderFrame, ordered⟩ :=
    EnumerationPartialCompletion.expandPartial_complete (boundaryView heap) level frontier fragment middle
      readStable.safe (stratified_read before middle level frontier readStable stratified) allocated
  let bound := readFuel + renderFuel
  have rootAt : Success (rootFragment bound) before fragment middle :=
    rootFragment_moreFuel readFuel renderFuel before fragment middle rootRead
  have renderedAt : Success (expandPartial heap bound fragment) middle observedTerm after := by
    simpa only [expandPartial, bound, Nat.add_comm] using
      EnumerationObservations.expandPartial_moreFuel (boundaryView heap) renderFuel readFuel fragment
        middle observedTerm after rendered
  have actual : Success (rootPartial heap bound) before observedTerm after :=
    (success_bind _ _ _ _ _).mpr ⟨fragment, middle, rootAt, renderedAt⟩
  have frame := EnumerationObservations.rootPartial_frame (boundaryView heap) bound before after
    observedTerm safe.1.total actual
  refine ⟨bound, observedTerm, after, ?_, readStable.trans renderStable, frame, ordered, ?_⟩
  · intro extra
    have raised := EnumerationObservations.rootPartial_moreFuel (boundaryView heap) bound extra
      before observedTerm after actual
    exact ⟨raised, root_exact heap (bound + extra) before after observedTerm raised⟩
  · intro language meaning assignment satisfied
    exact ⟨(SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning
      assignment before after frame).mpr satisfied,
      root_completes heap language meaning assignment bound before after observedTerm safe.1.total satisfied actual⟩

end MicroCFTA.SourcePruningEnumerationPartialOutput
