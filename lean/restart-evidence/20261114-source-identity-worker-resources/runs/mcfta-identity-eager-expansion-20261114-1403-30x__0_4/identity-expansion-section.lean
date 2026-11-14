section ActualIdentityEagerExpansion
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationSharedRecursive (CurrentPrefixFacts)
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound

/-- The actual identity checkpoint supplies every phase of one eager expansion. -/
private theorem identity_eager_expansion_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeWithNarrowComplete (Typing := Unit) (bits := bits)
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
      none (fun _ _ => none) formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Unit)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before = some (.expand uv)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf
        none (fun _ _ => none) (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  have firstReserved := nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned
  have finalGrowth := eagerFinal_ge (recursiveDepth + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
  have stageGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
  obtain ⟨prefixFuel, phases⟩ := SourcePruningEnumerationSharedRecursive.identity_checkpoint_resources
    graph checkEmpty edgesOf metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  rcases phases with ⟨checked, checkedMass, phase⟩ | ⟨checked, phase⟩ |
    ⟨handle, scs, value, after, _nonempty, _encoded, ready, stored, incoming, lengths, sameMass, phase⟩
  · have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata checked = some .stuck
    · have certificate : OutcomeResources (Typing := Unit) formulas solver caller seed
          (.complete [] caller memos.query) := by
        refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_, certificate.mono finalGrowth.1 finalGrowth.2⟩
      intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, observed]
    · let parkedSeed := advance start (ceiling + 1)
      let parkedMass := ceiling + ceiling
      have headGrowth : Le start.2 parkedSeed.2 ∧ start.1 ⊆ parkedSeed.1 :=
        ⟨SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge start (ceiling + 1),
          SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge start (ceiling + 1)⟩
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : mass checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound firstReserved.2
      have included := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
      have callbackResources : OutcomeResources formulas solver caller
          (fallbackPlan ceiling ceiling continuation start) outcome := resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, callbackResources.mono included.1 included.2⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, observed]
      dsimp only
      rw [framed]
      exact actual
  · let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
        ⟨caller.checked.native.machine.heap, caller.checked.operations⟩) caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
    have certificate : OutcomeResources (Typing := Unit) formulas solver caller start
        (.complete [] reached memos.query) := by
      refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
        current.2.2, rfl, query.symm, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, (phase extra).1]
    · exact certificate.mono stageGrowth.1 stageGrowth.2
  · let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
        ⟨caller.checked.native.machine.heap, caller.checked.operations⟩) caller.fourth caller.merge
    obtain ⟨prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      CurrentPrefixFacts.right_packet current.1
    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
        reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : mass after.core ≤ ceiling := by
      rw [sameMass]
      exact initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    obtain ⟨scanFuel, _observation, result, scanRun, certificate⟩ := eager_prepared_resources_with_narrow
      (fun _ _ _ node state => .done node state) graph [] checkEmpty edgesOf none (fun _ _ => none)
      formulas solver recursiveDepth recursive inventory reached middleMemos metadata after seed ceiling uv handle scs
      middlePacket ready stored incoming middleFits middleKnown currentMass inheritedLength
      selectionMembers selectionLength reserved
    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost⟩
    intro extra
    have currentPrefix := (phase (scanFuel + extra)).1
    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [common] at currentPrefix
    have actual := scanRun (prefixFuel + extra)
    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [scanCommon, middleQuery] at actual
    rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, currentPrefix]
    dsimp only
    rw [actual]

end ActualIdentityEagerExpansion
