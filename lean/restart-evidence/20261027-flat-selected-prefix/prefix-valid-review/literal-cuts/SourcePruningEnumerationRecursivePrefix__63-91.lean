/-- A current packet derives one common prefix fuel for its actual expansion decision. -/
theorem packet_prefix_complete (packet : Packet formulas solver inventory caller memos metadata before) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (bound + extra) selected caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          selected caller before memos.query) := by
  cases chosen : SourcePruningEnumerationRestart.decision stop order metadata before with
  | none =>
      refine ⟨0, ?_⟩
      intro _extra selected picked
      cases picked
  | some next =>
      cases next with
      | done | stuck =>
          refine ⟨0, ?_⟩
          intro _extra selected picked
          cases picked
      | expand selected =>
          obtain ⟨bound, completed⟩ := SourcePruningEnumerationSelectedStep.restart_prefix_complete
            holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
            caller memos before selected packet.context packet.safe packet.pending packet.valid chosen
          refine ⟨bound, ?_⟩
          intro extra target picked
          have same := Option.some.inj picked
          cases same
          exact completed extra
