theorem packet_prefix_complete (packet : Packet formulas solver inventory caller memos metadata before) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (bound + extra) selected caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          selected caller before memos.query) := by
  cases chosen : SourcePruningEnumerationRestart.decision stop order metadata before with
