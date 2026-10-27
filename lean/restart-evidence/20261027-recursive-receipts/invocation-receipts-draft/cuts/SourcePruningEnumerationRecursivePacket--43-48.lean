theorem captured_post (packet : Packet formulas solver inventory caller memos metadata before)
    (post : Post formulas solver next caller nextCaller final) :
    Packet formulas solver next nextCaller final metadata before :=
  ⟨post.context, packet.safe, packet.pending,
    SourcePruningEnumerationNativeBranchCompletion.cacheValid_post caller nextCaller before packet.valid post,
    packet.ordered, packet.bounded⟩
