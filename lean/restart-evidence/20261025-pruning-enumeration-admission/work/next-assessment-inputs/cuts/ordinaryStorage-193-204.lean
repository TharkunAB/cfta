            intro input member
            dsimp only [inputs] at member
            obtain ⟨indexed, _indexedMember, rfl⟩ := List.mem_map.mp member
            intro sc scMember
            rw [EnumerationSchedule.suspended_counter]
            rcases List.mem_append.mp scMember with inherited | ownMember
            · exact Nat.lt_of_lt_of_le
                (EnumerationSchedule.descend_bounded before.counter indexed.2 scs bounded sc inherited)
                (Nat.le_add_right _ _)
            · exact EnumerationSchedule.descend_bounded (before.counter + tries.length) indexed.2
                (suspendedVars before.counter tries)
                (EnumerationSchedule.suspended_bounded before.counter tries) sc ownMember)
