import MicroCFTA.SourceFlatPruningRendering

/-!
# Replay of complete native rendering

The original successful trace supplies each actual intermediate state.
The flat renderer keeps the same root term and ordered residual terms.
This theorem does not assert equivalence at insufficient original lookup fuel.
-/
namespace MicroCFTA.SourceFlatPruningRendering
open Language Fragments EnumerationFlatState EnumerationFlatReplay
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}
attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Replay the complete actual root and residual rendering at the supplied native heap. -/
theorem render_replays (native : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (fuel uv : Nat) :
    Replays (render (EnumGuard := EnumGuard) native marker fuel uv)
      (SourcePruningEnumerationRendering.render native marker fuel uv) := by
  apply bind_replays _ _ _ _ (expandUVar_replays native marker fuel uv)
  intro rendered flat earlier value after related observed
  obtain ⟨current, readState, reading, continued⟩ :=
    (EnumerationCorrectness.success_bind _ _ _ _ _).mp observed
  obtain ⟨currentSame, readSame⟩ := (EnumerationDriver.get_success earlier readState current).mp reading
  subst current readState
  obtain ⟨pending, guarded, traversal, final⟩ :=
    (EnumerationCorrectness.success_bind _ _ _ _ _).mp continued
  let action : EnumGuard × Fragment Symbol → Action Symbol EnumGuard (EnumGuard × Term Symbol) :=
    fun obligation => do pure (obligation.1, ← expandFragment native marker fuel obligation.2)
  let oldAction : EnumGuard × Fragment Symbol → EnumerationState.EnumerateM Symbol EnumGuard (EnumGuard × Term Symbol) :=
    fun obligation => do pure (obligation.1, ← SourcePruningEnumerationRendering.expandFragment native marker fuel obligation.2)
  have each : ∀ obligation, Replays (action obligation) (oldAction obligation) := by
    intro obligation
    exact bind_replays _ _ _ _ (expandFragment_replays native marker fuel obligation.2)
      (fun term => pure_replays (obligation.1, term))
  obtain ⟨flatGuarded, actual, finalRelated⟩ :=
    mapM_replays action oldAction each earlier.obligations flat earlier pending guarded related traversal
  obtain ⟨valueSame, afterSame⟩ :=
    (EnumerationCorrectness.success_pure (rendered, pending) value guarded after).mp final
  subst value after
  refine ⟨flatGuarded, ?_, finalRelated⟩
  change ((flat.obligations.mapM action >>= fun result => pure (rendered, result)) flat :
    List (Except EnumerationState.Error ((Term Symbol × List (EnumGuard × Term Symbol)) × State Symbol EnumGuard))) =
      [.ok ((rendered, pending), flatGuarded)]
  rw [EnumerationResultRelation.stateT_bind_rows]
  change (flat.obligations.mapM action flat : List (Except EnumerationState.Error _)).flatMap _ = _
  rw [related.obligations, actual]
  rfl

end MicroCFTA.SourceFlatPruningRendering
