theorem callback_complete (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment) :
    ∃ fuel result after,
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) := by
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨fuel, result, after, success, stable, frame, afterOrder, types, holes, typing, bounded⟩ :=
    recordTypes_inl_complete_bounded graph templates level frontier metadata uv fragment before.core
      packet.safe ordered allocated packet.bounded
  refine ⟨fuel, result, after,
    callback_frame packet result.2 after stable.safe frame ⟨level, frontier, afterOrder⟩ bounded,
    stable, frame, types, holes, typing, ?_⟩
  intro extra
  have more := recordTypes_moreFuel graph templates fuel extra metadata uv (.inl fragment)
    before.core result after success
  refine ⟨more, SourcePruningCallbackExact.recordTypes_exact graph templates (fuel + extra) metadata uv
    (.inl fragment) before.core after result more, ?_⟩
  intro recur stop order
  exact continueWith_exact recur graph templates stop order (fuel + extra) metadata uv fragment
    caller memos.query before result after more
