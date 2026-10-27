    cases pairSame
    have combinedBounded : ∀ sc ∈ scs ++ suspendedVars before.core.counter tries, sc.var < after.core.counter := by
      intro sc member
      rw [counter]
      rcases List.mem_append.mp member with inherited | own
      · have := bounded sc inherited
        omega
      · exact suspended_bounded before.core.counter tries sc own
    refine ⟨childrenAvailable indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember),
      childrenClosed indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember), ?_, ?_⟩
    · rw [← descend_append]
      exact descend_bounded _ indexed.2 _ combinedBounded
    · intro held fragment stored
      rw [← descend_append]
      exact descend_avoids _ held indexed.2 _ (combinedPending held fragment stored)
  · intro held inside root avoids
    have frame : EnumerationDriver.Protected held before.core after.core := by
      rw [coreSame]
      exact EnumerationDriver.suspension_protected held tries.length before.core safe inside root
    refine ⟨frame, ?_⟩
    have combinedAvoids : Avoids before.core.representatives held (scs ++ suspendedVars before.core.counter tries) := by
      intro sc member
      rcases List.mem_append.mp member with inherited | own
      · exact avoids sc inherited
      · exact fresh_avoids before.core safe.1 held inside tries sc own
    have afterAvoids := frame.avoids _ combinedAvoids
    intro incoming bucket member
    obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp member
    cases pairSame
    rw [← descend_append]
    exact descend_avoids _ held indexed.2 _ afterAvoids
