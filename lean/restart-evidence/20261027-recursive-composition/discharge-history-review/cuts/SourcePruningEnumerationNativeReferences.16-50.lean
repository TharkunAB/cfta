/-- Assimilation stores only references from its two actual pending slots. -/
theorem assimilated_allowed (allowed : Nat → Prop)
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (valid : ReferencesAllowed allowed before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs)) :
    ReferencesAllowed allowed (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
  have sourceInputs : InputsAllowed allowed sourceScs := valid _ (List.mem_of_getElem? sourceStored)
  have targetInputs : InputsAllowed allowed targetScs := valid _ (List.mem_of_getElem? targetStored)
  let middle := {before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))}
  have first : ReferencesAllowed allowed middle :=
    setValue_allowed allowed target _ before middle valid
      (fun sc member => (List.mem_append.mp member).elim (sourceInputs sc) (targetInputs sc))
      ((EnumerationDriver.modify_success _ _ _).mpr rfl)
  exact setValue_allowed allowed source .eliminated middle
    {middle with values := middle.values.set source .eliminated} first
    (by simp [InputsAllowed, references]) ((EnumerationDriver.modify_success _ _ _).mpr rfl)

/-- A native incoming write adds its supplied bucket to the actual current payload. -/
theorem incoming_written (allowed : Nat → Prop)
    (read after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (oldNode : Option Nat) (incomingScs oldScs : List Suspended)
    (valid : ReferencesAllowed allowed read) (inputs : InputsAllowed allowed incomingScs)
    (stored : read.values[target]? = some (.unenumerated oldNode oldScs))
    (written : after.values = read.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))) :
    ReferencesAllowed allowed after := by
  have oldInputs : InputsAllowed allowed oldScs := valid _ (List.mem_of_getElem? stored)
  intro value member
  rw [written] at member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid value old
  · subst value
    intro sc listed
    exact (List.mem_append.mp listed).elim (inputs sc) (oldInputs sc)
