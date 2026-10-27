/-- Every retained prefix cache carries the recursive packet at its actual native endpoint. -/
theorem prefix_packet (packet : Packet formulas solver inventory caller memos metadata before)
    (observed : SourcePruningEnumerationSelectedStep.Result width Typing)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .parked _ (some after) _ => Packet formulas solver inventory caller memos metadata after
    | .narrowed _ _ reached queries _ (some after) _ _ =>
        ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          Packet formulas solver inventory reached final metadata after
    | _ => True := by
  have cached := SourcePruningEnumerationPrefixPacket.prefix_cache_valid holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed valid
  have native := SourcePruningEnumerationPrefixPacket.prefix_context holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed valid
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨cacheValid, safe, pending, counter, ordered⟩ := cached
          refine ⟨packet.context, safe, pending, cacheValid, ?_, ?_⟩
          · obtain ⟨level, frontier, initial⟩ := packet.ordered
            exact ⟨level, frontier, ordered level frontier initial⟩
          · simpa only [counter] using packet.bounded
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨cacheValid, safe, pending, counter, ordered⟩ := cached
          obtain ⟨final, post, saved⟩ := native
          refine ⟨final, post, saved, post.context, safe, pending, cacheValid, ?_, ?_⟩
          · obtain ⟨level, frontier, initial⟩ := packet.ordered
            exact ⟨level, frontier, ordered level frontier initial⟩
          · simpa only [counter] using packet.bounded
