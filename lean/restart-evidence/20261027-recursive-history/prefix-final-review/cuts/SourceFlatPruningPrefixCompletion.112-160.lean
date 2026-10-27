/-- Retain the full old producer and certify its actual flat prefix at every sufficient bound. -/
theorem packet_prefix_complete
    (caller : Caller width) (memos : Memos) (before : OldCached) (flat : FlatCached)
    (related : EnumerationFlatCached.Related flat before)
    (packet : Packet formulas solver inventory caller memos metadata before) :
    ∃ bound,
      (∀ extra selected,
        SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
        SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (bound + extra) selected caller before memos
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query)) ∧
      ∀ extra selected,
        SourceFlatPruningRestart.decision stop order metadata flat = some (.expand selected) →
        ResultRelated
          (run holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) selected caller flat memos.query)
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query) ∧
        match run holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) selected caller flat memos.query with
        | .parked _ (some after) _ =>
            ∃ oldAfter : OldCached, EnumerationFlatCached.Related after oldAfter ∧
              Packet formulas solver inventory caller memos metadata oldAfter ∧
              EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap after
        | .narrowed _ _ reached queries _ candidate _ =>
            ∃ final : Memos, Post formulas solver inventory caller reached final ∧
              final.query = queries ∧
              match candidate with
              | none => True
              | some after =>
                  ∃ oldAfter : OldCached, EnumerationFlatCached.Related after oldAfter ∧
                    Packet formulas solver inventory reached final metadata oldAfter ∧
                    EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap after
        | _ => True := by
  obtain ⟨bound, original⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet
  refine ⟨bound, original, ?_⟩
  intro extra selected chosen
  have oldChosen := (SourceFlatPruningRestart.decision_related related stop order metadata).symm.trans chosen
  have valid := original extra selected oldChosen
  have actual := run_related_of_valid
    holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
    (bound + extra) selected caller before flat memos related valid
  exact ⟨actual, related_packet holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory (bound + extra) selected caller memos before packet _ _ valid actual⟩
