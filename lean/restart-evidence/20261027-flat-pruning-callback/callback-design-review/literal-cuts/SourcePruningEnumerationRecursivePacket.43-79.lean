theorem captured_post (packet : Packet formulas solver inventory caller memos metadata before)
    (post : Post formulas solver next caller nextCaller final) :
    Packet formulas solver next nextCaller final metadata before :=
  ⟨post.context, packet.safe, packet.pending,
    SourcePruningEnumerationNativeBranchCompletion.cacheValid_post caller nextCaller before packet.valid post,
    packet.ordered, packet.bounded⟩

/-- Safe callback reads transport the packet to their returned core and metadata. -/
theorem callback_frame (packet : Packet formulas solver inventory caller memos metadata before)
    (updated : Metadata Typing) (after : Core) (safe : EnumerationSchedule.Safe after)
    (frame : EnumerationCompressionFrame.Frame before.core after)
    (ordered : ∃ level frontier, EnumerationOrder.Stratified after level frontier)
    (bounded : ∀ group ∈ updated.pending, SourcePruningPartialMatch.PendingBound after.counter group) :
    Packet formulas solver inventory caller memos updated (EnumerationExpandableIndex.frame after before) := by
  refine ⟨packet.context, safe, ?_,
    SourcePruningEnumerationNativeBranchCompletion.cacheValid_frame caller before after frame safe packet.valid,
    ordered, bounded⟩
  exact EnumerationPendingReplacement.frame_pending before.core after frame packet.pending

/-- An actual completed receipt derives the restart packet before callback execution. -/
theorem receipt_packet (originalCore : Core) (target : Nat) (fragment : Fragments.Fragment Symbol)
    (after : Cached) (level : Nat → Nat) (frontier : Nat)
    (context : Context formulas solver inventory caller memos)
    (admitted : SourcePruningEnumerationNativeBranchCompletion.Admitted target
      (.complete fragment caller memos.query after))
    (history : SourcePruningEnumerationNativeBranchCompletion.FragmentHistory originalCore
      (.complete fragment caller memos.query after))
    (pending : EnumerationReferences.PendingReferences after.core)
    (ordered : EnumerationOrder.Stratified originalCore level frontier)
    (bounded : ∀ group ∈ metadata.pending, SourcePruningPartialMatch.PendingBound originalCore.counter group) :
    Packet formulas solver inventory caller memos metadata after := by
  obtain ⟨nextLevel, afterOrder⟩ := history.2.2 level frontier ordered
  refine ⟨context, admitted.2.1, pending, admitted.1, ⟨nextLevel, frontier + 1, afterOrder⟩, ?_⟩
  intro group member entry listed
  exact Nat.lt_of_lt_of_le (bounded group member entry listed) history.1

end MicroCFTA.SourcePruningEnumerationRecursive
