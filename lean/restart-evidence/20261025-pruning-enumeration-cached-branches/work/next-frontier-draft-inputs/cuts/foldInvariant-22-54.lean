theorem assimilated_preserves
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat)
    (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (roots : Nat → Nat) (waiting : EnumerationWaitingIndex.Waiting)
    (storage : StorageValid before)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (different : target ≠ source) :
    StorageValid (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) ∧
      EnumerationCanonicalWaiting.Correct roots
        (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values waiting
 := by
  have sourceBound : SlotBound before.counter (.unenumerated sourceNode sourceScs : UVarValue Symbol) := by
    exact storage.values _ (List.mem_of_getElem? sourceStored)
  have targetBound : SlotBound before.counter (.unenumerated targetNode targetScs : UVarValue Symbol) := by
    exact storage.values _ (List.mem_of_getElem? targetStored)
  have mergedBound : SlotBound before.counter (.unenumerated merged (sourceScs ++ targetScs) : UVarValue Symbol) := by
    intro sc member
    rcases List.mem_append.mp member with sourceMember | targetMember
    · exact sourceBound sc sourceMember
    · exact targetBound sc targetMember
  have first : StorageValid {before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))} := by
    exact set_storage before storage target (.unenumerated merged (sourceScs ++ targetScs)) mergedBound
  have second : StorageValid {{before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))} with
      values := (before.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set source .eliminated} := by
    exact set_storage _ first source .eliminated trivial
  exact ⟨⟨second.aligned, second.total, second.forest, second.values, second.guards⟩,
    EnumerationCanonicalWaiting.assimilation_correct roots before.values target source
      (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs)
      (.unenumerated merged (sourceScs ++ targetScs)) different sourceStored targetStored rfl waiting counts⟩

