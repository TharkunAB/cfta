import MicroCFTA.EnumerationConstruction

/-!
# Constructing selected-root expansions

A ready pending root with a satisfying assignment has an actual expansion.
The final root write records the constructed fragment equation.
-/

namespace MicroCFTA.EnumerationOutConstruction
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- A bounded live root can be read by the actual value action at a sufficient bound. -/
theorem getValue_terminates (before : State Symbol Guard) (safe : Safe before) (uv : Nat)
    (root : IsRoot before.representatives uv) (value : UVarValue Symbol) (stored : before.values[uv]? = some value) :
    ∃ fuel after, Success (getValue fuel uv) before value after := by
  obtain ⟨fuel, result, after, lookup, _⟩ := representative_terminates before safe.1.total uv
  obtain ⟨found, foundLookup, resultSame, afterSame⟩ := (representative_success fuel uv before after result).mp lookup
  obtain ⟨size, rootPath⟩ := root
  have same : result = uv := resultSame.trans (UnionFind.reaches_unique (UnionFind.findRoot_correct fuel before.representatives uv found foundLookup).1 rootPath).1
  refine ⟨fuel, after, (success_bind _ _ _ _ _).mpr ⟨uv, after, by simpa only [same] using lookup, ?_⟩⟩
  exact (rawValue_success _ _ _ _).mpr ⟨by simpa [afterSame] using stored, rfl⟩

/-- A correct fragment equation preserves the complete assignment when stored at its variable. -/
theorem write_equation_satisfies (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : State Symbol Guard) (uv : Nat) (fragment : Fragment Symbol)
    (inside : uv < before.values.length) (satisfies : Satisfies language meaning assignment before)
    (equation : fill assignment fragment = assignment uv) :
    Satisfies language meaning assignment {before with values := before.values.set uv (.enumerated fragment)} := by
  refine ⟨⟨satisfies.1.1, ?_⟩, satisfies.2⟩
  intro other
  by_cases same : other = uv
  · subst other
    simpa [heap, inside, slot, slotSatisfies] using equation
  · simpa [heap, Ne.symm same] using satisfies.1.2 other

/-- Each ready pending graph root has a successful actual expansion that preserves its witnessed term. -/
theorem enumerateOut_complete (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (before : State Symbol Guard) (assignment : Nat → Term Symbol) (uv node : Nat) (scs : List Suspended)
    (ready : Ready uv before) (canonical : Canonical before) (pending : PendingReferences before)
    (stored : before.values[uv]? = some (.unenumerated (some node) scs))
    (satisfies : Satisfies (Accepted graph meaning) meaning assignment before) :
    ∃ fuel fragment after extended, Success (enumerateOut graph fuel uv) before fragment after ∧
      Satisfies (Accepted graph meaning) meaning extended after ∧
      (∀ index < before.counter, extended index = assignment index) ∧ fill extended fragment = assignment uv := by
  obtain ⟨readFuel, readState, reading⟩ := getValue_terminates before ready.safe uv ready.root _ stored
  obtain ⟨readSafe, readCounter, readFrame, readStored⟩ := getValue_root readFuel uv before readState _ ready.safe ready.inside ready.root reading
  have readStable := (getValue_storage readFuel uv before readState _ ready.safe ready.inside reading).1
  have readSatisfies := (getValue_assignment (Accepted graph meaning) meaning assignment readFuel uv before readState _ ready.safe.1.total reading).mpr satisfies
  have readPending := pending_read before readState readStable pending
  obtain ⟨resolveFuel, resolvedRoot, resolved, resolution, _⟩ := representative_terminates readState readSafe.1.total uv
  obtain ⟨rootSame, resolvedSafe, resolvedCounter, resolvedFrame⟩ := representative_root resolveFuel uv resolvedRoot readState resolved readSafe
    (by simpa [readCounter] using ready.inside) readFrame.root resolution
  subst resolvedRoot
  have resolvedStable := representative_read resolveFuel uv uv readState resolved readSafe (by simpa [readCounter] using ready.inside) resolution
  have resolvedSatisfies := (representative_assignment (Accepted graph meaning) meaning assignment resolveFuel uv uv readState resolved readSafe.1.total resolution).2.mpr readSatisfies
  have resolvedPending := pending_read readState resolved resolvedStable readPending
  have resolvedStored : resolved.values[uv]? = some (.unenumerated (some node) scs) := resolvedFrame.value.trans readStored
  let started := {resolved with expansionAncestry := resolved.recursionAncestry uv}
  have startedSafe : Safe started := ancestry_safe resolved _ resolvedSafe
  have startedSatisfies : Satisfies (Accepted graph meaning) meaning assignment started := resolvedSatisfies
  have inputBounds : ∀ sc ∈ scs, sc.var < started.counter := by
    exact resolvedSafe.1.values _ (List.mem_of_getElem? resolvedStored)
  have inputValid : ValidSuspended scs := canonical _ (List.mem_of_getElem? stored)
  have inputPending : InputsPending started scs := pending_inputs resolved resolvedPending uv (some node) scs resolvedStored
  have inputHolds := stored_satisfies (Accepted graph meaning) meaning assignment before satisfies uv _ stored
  have accepted : Accepted graph meaning node (assignment uv) := inputHolds.1
  have constraints : ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
    intro sc member
    exact inputHolds.2 _ (List.mem_map.mpr ⟨sc, member, rfl⟩)
  obtain ⟨nodeFuel, fragment, expanded, extended, expansion, expandedSatisfies, extendedAgree, exactTerm⟩ :=
    enumerateNode_complete graph meaning complete correct node (assignment uv) accepted started assignment scs startedSafe inputValid inputBounds inputPending startedSatisfies constraints
  obtain ⟨expandedSafe, growth, _⟩ := (enumeration_safety graph nodeFuel).1 scs node started expanded fragment startedSafe inputBounds expansion
  have insideStarted : uv < started.counter := by simpa [started, resolvedCounter, readCounter] using ready.inside
  have insideExpanded : uv < expanded.values.length := by
    rw [← expandedSafe.1.aligned]
    exact Nat.lt_of_lt_of_le insideStarted growth
  let cleared := {expanded with expansionAncestry := []}
  let after := {cleared with values := cleared.values.set uv (.enumerated fragment)}
  have afterSatisfies : Satisfies (Accepted graph meaning) meaning extended after :=
    write_equation_satisfies (Accepted graph meaning) meaning extended cleared uv fragment insideExpanded expandedSatisfies
      (exactTerm.trans (extendedAgree uv insideStarted).symm)
  let fuel := readFuel + resolveFuel + nodeFuel
  have readMore : Success (getValue (fuel + 1) uv) before (.unenumerated (some node) scs) readState := by
    have more := getValue_moreFuel readFuel (resolveFuel + nodeFuel + 1) uv before _ readState reading
    simpa [fuel, Nat.add_assoc] using more
  have resolveMore : Success (representative (fuel + 1) uv) readState uv resolved := by
    have more := representative_moreFuel resolveFuel (readFuel + nodeFuel + 1) uv readState uv resolved resolution
    simpa [fuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using more
  have expansionMore : Success (enumerateNode graph fuel scs node) started fragment expanded := by
    have more := (enumeration_moreFuel graph nodeFuel (readFuel + resolveFuel)).1 scs node started fragment expanded expansion
    simpa [fuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using more
  refine ⟨fuel, fragment, after, extended, ?_, afterSatisfies, ?_, exactTerm⟩
  · unfold enumerateOut
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨.unenumerated (some node) scs, readState, readMore, ?_⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨uv, resolved, resolveMore, ?_⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨resolved, resolved, (get_success _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
    dsimp only
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨(), started, (modify_success _ _ _).mpr ?_, ?_⟩
    · cases view : graph.node node
      all_goals first | rfl | exact (complete.1 node _ view).elim
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨fragment, expanded, ?_, ?_⟩
    · cases view : graph.node node
      all_goals first | exact expansionMore | exact (complete.1 node _ view).elim
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨(), cleared, (modify_success _ _ _).mpr rfl, ?_⟩
    exact (success_bind _ _ _ _ _).mpr ⟨(), after, (modify_success _ _ _).mpr rfl, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
  · intro index inside
    exact extendedAgree index (by simpa [started, resolvedCounter, readCounter] using inside)

end MicroCFTA.EnumerationOutConstruction
