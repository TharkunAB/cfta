# General actual eager resources at fixed recursion depth

Base: b9b9e0799616faad626a4fc1dc55173b58950087.
Main: e53852064d3ef5a2eafec47d754c27504b11de5f, fetched unchanged at 2026-11-13 03:19 CET.
The existing module has 3093 lines. It retains all three public arithmetic
laws and adds runEager_finite_complete_resources. The exact original public
20-line target is unchanged. The complete old module body remains an exact
prefix before the new proof sections. All execution and mathematical plan
and reservation definitions remain unchanged.

For any fixed recursive depth, current Packet, Fits, Heap, selection facts,
suspended-mass bound and computed eagerReserved, one finite common work bound
exists. Every larger common work fuel returns the SAME actual runEager outcome.
The ENTIRE existing OutcomeResources predicate holds at eagerFinal. Each
output retains its own packet and native caller endpoint. Full Memos and query
facts, the final Post, computed capacities and guard alphabet remain. Stopped
prefixes and their actual optional endpoints remain. No public child, consumer,
callback, future Packet, role, work, model or lower-depth provider is supplied.

The opaque proof uses ONE actual opaque resource producer and the SAME receipt
and continuation. It pads the actual scs.length+1 schedule within ceiling+1.
Native empty, rejected and stopped outcomes retain their literal observations.
The common preparation proof uses ONE complete_resources_current producer.
It derives current native height and captured shape internally. Ordinary
nodes use the checked actual captured-row scan. Other values use the checked
actual opaque branch. The SAME preparation and scan fuels are aligned to one
common work bound. Full Post, Memos, query and resource records are composed.

The actual expansion proof observes the SAME selected prefix through the
resource and PrefixValid producers at one common sufficient fuel. Parked
states retain their actual Restart framing and computed fallback admission.
Native-empty and accepted narrowed states retain their actual endpoints.
Accepted preparation invokes the checked common preparation result. Honest
Nat induction closes every PRIVATE concrete lower-depth resume premise.
The public wrapper uses the literal unchanged eager entry adapter.

The raw preparation and first closure candidates hit Lean's deterministic
normalization limit. The checked proof keeps nodeReserved, nodePlan and the
existing headProfile forecast locally irreducible ONLY inside new sections.
The known successor node reservation and plan are unfolded explicitly where
needed. These attributes control elaboration. They do not change definitions
or add assumptions. Global options, heartbeat and linter limits remain. The
raw failed sources, intermediate repairs and exact headers remain below.
Every stage is hash-pinned. Reverse patches reconstruct each exact source.

The strongest original-input Program output contract still uses the SHALLOW
worker. The separate exact original-source language law has a completed
nodeCall endpoint. General eager Program roles and shared backward model
history, satisfying Type-assignment existence, output/depth adequacy and the
full default Haskell path remain open. Resource preservation does not imply
source typing, a model or output existence. Streams, lazy demand, order,
multiplicity, both inverse laws and host capacity remain separate contracts.
No Haskell source changed. No Haskell tests were repeated. External Liquid
repair ownership is unchanged. These local Lean elaboration repairs are not
Haskell defects. The existing preparation producer already retains whole-cache
same-assignment satisfaction equivalence; the pinned audit below explains it.
The later-output history and model-existence gaps remain.

## Public declarations

Source SHA256 `07219c234019081e7bcfe03d2c714eca723e0d7de3a7e7882272b2a2801b2de4`.

```lean
theorem eagerFinal_ge (depth : Nat) (seed : Seed) (ceiling : Nat) :
    Le seed.2 (eagerFinal depth seed ceiling).2 ∧
      seed.1 ⊆ (eagerFinal depth seed ceiling).1
```

```lean
theorem first_row_callback_le_final (depth : Nat) (seed : Seed) (ceiling : Nat)
    (positive : 0 < scalar (preparedSeed seed).2) :
    let captured := preparedSeed seed
    let N := scalar captured.2
    let b := ceiling + SourcePruningEnumerationGuardWidth.width captured.1
    let rowStart := eagerFinal depth (advance captured (ceiling + 1)) (ceiling + ceiling)
    let first := eagerFinal depth (advance rowStart (N * (b + 1))) (ceiling + N * b)
    let whole := eagerFinal (depth + 1) seed ceiling
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1
```

```lean
theorem eagerReserved_of_final_room (bits depth : Nat) (seed : Seed) (ceiling : Nat)
    (room : Room bits (eagerFinal depth seed ceiling).2) :
    eagerReserved bits depth seed ceiling
```

```lean
theorem runEager_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome
```

## Replayed source history

Start from live checked3093. Apply these reverse patches in order.
Each patch was applied with GNU patch --output and matched exact target bytes.
Earlier stages remain in the preceding checkpoints.

```json
[
  {
    "stage": "checked2487",
    "lines": 2487,
    "source_sha256": "e1f26f5a64b7d91af08065a837509e56d9d274c6eef849b10cc296631248055e",
    "compiler_exit": 0,
    "new_public_laws_checked": 0
  },
  {
    "stage": "checked2607",
    "lines": 2607,
    "source_sha256": "2a22e0b2e012c358828766e1d5a472f822345d7fe80aeca38c8eafcefa512083",
    "compiler_exit": 0,
    "new_public_laws_checked": 0
  },
  {
    "stage": "failed2816",
    "lines": 2816,
    "source_sha256": "10b4d69e70a3761cd47721f53d66849455fd3f21543deb7f88c326a196aa4098",
    "compiler_exit": 1,
    "new_public_laws_checked": 0
  },
  {
    "stage": "failed2817",
    "lines": 2817,
    "source_sha256": "5fdb979ae8666644f8b8743275be19f7a93f06bb7f528998e74d35649e359ec5",
    "compiler_exit": 1,
    "new_public_laws_checked": 0
  },
  {
    "stage": "failed2819",
    "lines": 2819,
    "source_sha256": "45d7c2b04cdd2b36fba510749d6db3547f5737c55f7e232915784c2b221512b9",
    "compiler_exit": 1,
    "new_public_laws_checked": 0
  },
  {
    "stage": "failed2821",
    "lines": 2821,
    "source_sha256": "bbad00f5d3aeadb857e25b4e4b48b42126e41721d10b659a4f2a991dcaa1027e",
    "compiler_exit": 1,
    "new_public_laws_checked": 0
  },
  {
    "stage": "checked2822",
    "lines": 2822,
    "source_sha256": "e53a8a310847e8e91be89f031748f4935c6740d7d30c27031f1c22fb71b150fb",
    "compiler_exit": 0,
    "new_public_laws_checked": 0
  },
  {
    "stage": "failed3091",
    "lines": 3091,
    "source_sha256": "9f623c8b284a56d2596fd17f0c22d5e7b899bec9dbf618d299e8bcdd10b3367d",
    "compiler_exit": 1,
    "new_public_laws_checked": 0
  },
  {
    "stage": "checked3093",
    "lines": 3093,
    "source_sha256": "07219c234019081e7bcfe03d2c714eca723e0d7de3a7e7882272b2a2801b2de4",
    "compiler_exit": 0,
    "new_public_laws_checked": 1
  }
]
```

### checked3093 to failed3091

```diff
--- checked3093.lean
+++ failed3091.lean
@@ -3014,2 +3013,0 @@
-attribute [local irreducible] nodeReserved nodePlan
-attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
```

### failed3091 to checked2822

```diff
--- failed3091.lean
+++ checked2822.lean
@@ -1,2 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
-import MicroCFTA.SourcePruningEnumerationPrefixMass
@@ -2824,267 +2821,0 @@
-section ActualEagerExpansion
-attribute [local irreducible] nodeReserved nodePlan
-attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-open SourcePruningEnumerationSelectedStep (runPrefix)
-open SourcePruningEnumerationSharedRecursive (checkpoint_resources CurrentPrefixFacts)
-local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
-
-private theorem eager_expansion_resources
-    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
-      checkEmpty edgesOf stop order formulas solver recursiveDepth)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
-    (uv : Nat) (seed : Seed) (ceiling : Nat)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (bounded : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
-    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
-    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
-    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) (recursiveDepth + 1)
-        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
-      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome := by
-  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
-  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
-  let own := SourcePruningEnumerationGuardWidth.width start.1
-  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
-  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
-  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
-      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
-  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
-    simpa only [eagerReserved] using reserved
-  have firstReserved := nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned
-  have finalGrowth := eagerFinal_ge (recursiveDepth + 1) seed ceiling
-  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
-  have stageGrowth := nodePlan_ge limit own limit ceiling ceiling continuation growth start
-  obtain ⟨currentFuel, phases⟩ := checkpoint_resources holeKey keyMatches admits graph templates checkEmpty edgesOf
-    stop order metadata formulas solver inventory caller memos before packet seed.2
-    (fun guard => guard ∈ seed.1) bounded known uv chosen
-  obtain ⟨legacyFuel, legacyComplete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
-    holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
-    caller memos before packet
-  let prefixFuel := currentFuel + legacyFuel
-  have shift (extra : Nat) : currentFuel + (legacyFuel + extra) = prefixFuel + extra := by
-    dsimp only [prefixFuel]
-    omega
-  have legacy (extra : Nat) : SourcePruningEnumerationSelectedStep.PrefixValid
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
-      (prefixFuel + extra) uv caller before memos
-      (runPrefix holeKey keyMatches admits graph templates stop order metadata
-        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
-        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query) := by
-    have valid := legacyComplete (currentFuel + extra) uv chosen
-    have common : legacyFuel + (currentFuel + extra) = prefixFuel + extra := by
-      dsimp only [prefixFuel]
-      omega
-    simpa only [common] using valid
-  rcases phases with ⟨checked, originalPhase⟩ | ⟨checked, heap, originalPhase⟩ |
-    ⟨checked, phaseValue, heap, after, _nonempty, originalPhase⟩
-  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
-    simp only [shift] at phase
-    have facts := (phase 0).2.1
-    rw [(phase 0).1] at facts
-    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
-    have same : checked = cached := Option.some.inj sameCache
-    subst cached
-    have valid := legacy 0
-    rw [(phase 0).1] at valid
-    have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
-      (prefixFuel + 0) uv caller memos before packet _ valid (phase 0).1
-    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
-      cases checked
-      rfl
-    by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
-    · have certificate : OutcomeResources (Typing := Typing) formulas solver caller seed
-          (.complete [] caller memos.query) := by
-        refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
-        intro output member
-        exact (List.not_mem_nil member).elim
-      refine ⟨prefixFuel, .complete [] caller memos.query, ?_, certificate.mono finalGrowth.1 finalGrowth.2⟩
-      intro extra
-      have observed := (phase extra).1
-      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
-      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, observed]
-    · let parkedSeed := advance start (ceiling + 1)
-      let parkedMass := ceiling + ceiling
-      have headGrowth : Le start.2 parkedSeed.2 ∧ start.1 ⊆ parkedSeed.1 :=
-        ⟨SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge start (ceiling + 1),
-          SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge start (ceiling + 1)⟩
-      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
-      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
-        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
-      have massBound : mass checked.core ≤ parkedMass :=
-        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
-      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
-        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
-        selectionMembers selectionLength massBound firstReserved.2
-      have included := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
-      have callbackResources : OutcomeResources formulas solver caller
-          (fallbackPlan ceiling ceiling continuation start) outcome := resources
-      refine ⟨prefixFuel + resumeFuel, outcome, ?_, callbackResources.mono included.1 included.2⟩
-      intro extra
-      have observed := (phase (resumeFuel + extra)).1
-      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
-      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
-      have actual := running (prefixFuel + extra)
-      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
-      rw [recursiveCommon] at actual
-      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, observed]
-      dsimp only
-      rw [framed]
-      exact actual
-  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
-    simp only [shift] at phase
-    let reached := SourceCurrentAllocatedPartialState.advance caller
-      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
-      caller.fourth caller.merge
-    have current := (phase 0).2
-    rw [(phase 0).1] at current
-    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
-      _prepared, _reached, post, query, _shape⟩ := current.1
-    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
-      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
-    have certificate : OutcomeResources (Typing := Typing) formulas solver caller start
-        (.complete [] reached memos.query) := by
-      refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
-        current.2.2, rfl, query.symm, ?_⟩
-      intro output member
-      exact (List.not_mem_nil member).elim
-    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
-    · intro extra
-      rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, (phase extra).1]
-    · exact certificate.mono stageGrowth.1 stageGrowth.2
-  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
-    simp only [shift] at phase
-    let reached := SourceCurrentAllocatedPartialState.advance caller
-      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
-      caller.fourth caller.merge
-    obtain ⟨_action, prefixAt, current⟩ := phase 0
-    rw [prefixAt] at current
-    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
-      CurrentPrefixFacts.right_packet current.1
-    have valid := legacy 0
-    rw [prefixAt] at valid
-    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
-      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
-      bounded known _ valid
-    obtain ⟨handle, scs, _value, _oldMemos, _oldPost, _oldQuery, _oldPacket, ready, stored,
-      _decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
-      _oldFits, _oldKnown⟩ := admission
-    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
-        reached.checked := current.2.1
-    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
-    have currentMass : mass after.core ≤ ceiling := Nat.le_trans
-      (SourcePruningEnumerationPrefixMass.retained_le holeKey keyMatches admits graph templates checkEmpty edgesOf
-        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt)
-      initialMass
-    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
-    obtain ⟨scanFuel, _observation, result, scanRun, certificate⟩ := eager_prepared_resources
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
-      inventory reached middleMemos metadata after seed ceiling uv handle scs middlePacket ready stored incoming
-      middleFits middleKnown currentMass inheritedLength selectionMembers selectionLength reserved
-    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost⟩
-    intro extra
-    obtain ⟨currentAction, currentPrefix, _current⟩ := phase (scanFuel + extra)
-    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
-    rw [common] at currentPrefix
-    have actual := scanRun (prefixFuel + extra)
-    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
-    rw [scanCommon, middleQuery] at actual
-    rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild, currentPrefix]
-    dsimp only
-    rw [actual]
-
-end ActualEagerExpansion
-
-section ActualEagerDepthClosure
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem eager_resume_complete
-    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (recursiveDepth : Nat) :
-    EagerResumeComplete (Typing := Typing) (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
-      stop order formulas solver recursiveDepth := by
-  induction recursiveDepth with
-  | zero =>
-      exact eager_resume_zero_complete holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver
-  | succ depth ih =>
-      intro inventory caller memos before metadata seed ceiling packet bounded known
-        selectionMembers selectionLength initialMass reserved
-      have growth := eagerFinal_ge (depth + 1) seed ceiling
-      cases decision : SourcePruningEnumerationRestart.decision stop order metadata before with
-      | none =>
-          obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
-            checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata none seed packet bounded known
-          refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
-          intro extra
-          simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] using running extra
-      | some selected =>
-          cases selected with
-          | done =>
-              obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
-                checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata (some .done) seed
-                packet bounded known
-              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
-              intro extra
-              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] using running extra
-          | stuck =>
-              obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey keyMatches admits graph templates
-                checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata (some .stuck) seed
-                packet bounded known
-              refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
-              intro extra
-              simpa only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild] using running extra
-          | expand uv =>
-              exact eager_expansion_resources holeKey keyMatches admits graph templates checkEmpty edgesOf stop order
-                formulas solver depth ih inventory caller memos before metadata uv seed ceiling packet bounded known
-                selectionMembers selectionLength initialMass reserved decision
-
-/-- Current reservations give one stable eager outcome and retain every output resource. -/
-theorem runEager_finite_complete_resources
-    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula)
-    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
-    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
-    (seed : Seed) (ceiling : Nat)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (bounded : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
-    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
-    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling) :
-    ∃ bound outcome,
-      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
-        metadata caller memos.query before = outcome) ∧
-      OutcomeResources formulas solver caller
-        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome  := by
-  have complete := eager_resume_complete (Typing := Typing) (bits := bits) holeKey fits admits graph templates
-    checkEmpty edgesOf stop order formulas solver recursiveFuel
-  obtain ⟨fuel, outcome, running, resources⟩ := complete inventory caller memos before metadata seed ceiling
-    packet bounded known selectionMembers selectionLength initialMass reserved
-  exact ⟨fuel, outcome, fun extra => running extra, resources⟩
-
-end ActualEagerDepthClosure
-
```

### checked2822 to failed2821

```diff
--- checked2822.lean
+++ failed2821.lean
@@ -2611 +2610,0 @@
-attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
```

### failed2821 to failed2819

```diff
--- failed2821.lean
+++ failed2819.lean
@@ -2610 +2610 @@
-attribute [local irreducible] nodeReserved nodePlan
+attribute [local irreducible] nodeReserved
@@ -2733,3 +2733 @@
-        _ = iterate row first limit := by
-          unfold nodePlan
-          rfl
+        _ = iterate row first limit := rfl
```

### failed2819 to failed2817

```diff
--- failed2819.lean
+++ failed2817.lean
@@ -2610 +2609,0 @@
-attribute [local irreducible] nodeReserved
@@ -2704 +2702,0 @@
-    unfold nodeReserved at computed
```

### failed2817 to failed2816

```diff
--- failed2817.lean
+++ failed2816.lean
@@ -2667,2 +2667 @@
-  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
-    simpa only [eagerReserved] using reserved
+  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := reserved
```

### failed2816 to checked2607

```diff
--- failed2816.lean
+++ checked2607.lean
@@ -1,2 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedEagerCapturedBounds
-import MicroCFTA.SourcePruningEnumerationSelectedPreparationCurrent
@@ -2609,207 +2606,0 @@
-section ActualPreparedResources
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-open SourcePruningEnumerationFiniteReservation (iterate)
-
-private theorem eager_prepared_resources
-    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
-      checkEmpty edgesOf stop order formulas solver recursiveDepth)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (ready : EnumerationDriver.Ready uv before.core)
-    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
-    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
-    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (bucketBound : scs.length ≤ ceiling)
-    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
-    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
-    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling) :
-    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
-      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
-          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
-          graph templates stop order (fuel + extra) metadata uv)
-        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
-          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
-      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) := by
-  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
-  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
-  let own := SourcePruningEnumerationGuardWidth.width start.1
-  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
-  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
-  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
-    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
-    graph templates stop order work metadata uv
-  change ∃ fuel observed outcome,
-    (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
-      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-      (hook (fuel + extra)) checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
-        (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
-    OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
-  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
-      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
-  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := reserved
-  obtain ⟨preparationFuel, decoded, value, heap, entered, retained,
-    preparedFits, _valueMass, preparedKnown, frame, enteredIncoming, sameMass⟩ :=
-    SourcePruningEnumerationSelectedPreparation.complete_resources_current
-      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
-      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 fits incoming
-      (fun guard => guard ∈ seed.1) known
-  obtain ⟨preparationRun, _decodedLookup, preparationPost, enteredPacket, _stable, enteredReady,
-    enteredStored, _counter, _values, _flags, _waiting, available, closed, _meaning, _satisfaction⟩ := retained
-  let preparedCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
-  have currentFits : Fits start.2 preparedCaller.checked := preparedFits
-  have currentKnown : Heap (fun guard => guard ∈ start.1) preparedCaller.checked.native.machine.heap := preparedKnown
-  have currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core ≤ ceiling := by
-    rw [sameMass]
-    exact mass
-  by_cases ordinary : ∃ entry rows depth free,
-      value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
-  · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
-    subst value
-    let captured := preparedCaller.checked.native.machine.heap
-    obtain ⟨heights, shapes⟩ := SourcePruningEnumerationSharedEagerCapturedBounds.captured_payload_bounds
-      start captured enteredPacket.context.ready.semantic.ready.semantic.1.normal.facts.linked
-      (SourceCurrentConstrainedCapRequiredResources.of_checked currentFits) currentKnown
-    have nodeHeight := heights (.node entry rows depth free) available
-    have positive : 0 < limit := by
-      change MergedOrdinaryHeight.edgesHeight rows + 1 ≤ limit at nodeHeight
-      omega
-    let height := limit - 1
-    have heightSame : height + 1 = limit := by dsimp only [height]; omega
-    have ranked : MergedOrdinaryHeight.height (.node entry rows depth free) ≤ height + 1 := by
-      rw [heightSame]
-      exact nodeHeight
-    have computed : nodeReserved bits limit own (height + 1) ceiling ceiling continuation admitted start := by
-      rw [heightSame]
-      exact planned
-    let first := fallbackPlan ceiling ceiling continuation start
-    let row := fun current => tuplePlan (nodePlan limit own height) limit (ceiling + own) ceiling continuation current
-    have firstGrowth := fallbackPlan_ge ceiling ceiling continuation growth start
-    have firstKnown : Heap (fun guard => guard ∈ first.1) preparedCaller.checked.native.machine.heap := by
-      intro key edge found
-      exact firstGrowth.2 (currentKnown key edge found)
-    have rowReserved : ∀ index, index < limit →
-        tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-          limit (ceiling + own) ceiling continuation admitted (iterate row first index) := computed.2
-    have length : (edgesOf (.node entry rows depth free)).length ≤ limit :=
-      Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
-    have bounded : ∀ sc ∈ scs, sc.var < entered.core.counter :=
-      enteredReady.safe.1.values _ (List.mem_of_getElem? enteredStored)
-    have pending := EnumerationReferences.pending_inputs entered.core enteredPacket.pending uv (some handle) scs enteredStored
-    obtain ⟨branchFuel, outcome, branchRun, certificate⟩ := eager_captured_rows_resources
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
-      captured limit own height limit inventory preparedCaller memos metadata entered first ceiling ceiling scs uv handle
-      enteredPacket enteredReady enteredStored enteredIncoming (currentFits.mono firstGrowth.1) firstKnown
-      (SourceEqualityRequiredCache.pure_keeps captured enteredPacket.context.ready.semantic.ready)
-      currentMass bucketBound entry rows depth free available closed ranked bounded pending
-      (edgesOf (.node entry rows depth free)) length (selectionMembers entry rows depth free) shapes
-      selectionMembers selectionLength rowReserved
-    have finalSame : eagerFinal (recursiveDepth + 1) seed ceiling = iterate row first limit := by
-      change nodePlan limit own limit ceiling ceiling continuation start = _
-      calc
-        nodePlan limit own limit ceiling ceiling continuation start =
-            nodePlan limit own (height + 1) ceiling ceiling continuation start :=
-          congrArg (fun h => nodePlan limit own h ceiling ceiling continuation start) heightSame.symm
-        _ = iterate row first limit := rfl
-    have resources : OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling)
-        (finish uv outcome) := by
-      rw [finalSame]
-      exact certificate.post preparationPost
-    refine ⟨preparationFuel + branchFuel,
-      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done (.node entry rows depth free) heap)),
-      outcome, ?_, resources⟩
-    intro extra
-    have atPreparation := preparationRun (branchFuel + extra)
-    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
-    rw [prepSame] at atPreparation
-    have atBranch := branchRun (preparationFuel + extra)
-    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
-    rw [branchSame] at atBranch
-    unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
-    rw [atPreparation]
-    simp only [nonterminal, Bool.false_eq_true, ↓reduceIte]
-    rw [frame, atBranch]
-  · have dispatch : (match (generalizing := false) value with
-        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false := by
-      cases value with
-      | node entry rows depth free =>
-          cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
-          | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
-          | true => rfl
-      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ => rfl
-    obtain ⟨branchFuel, receipt, outcome, rawRun, receiptRun, certificate⟩ := eager_opaque_resources
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
-      inventory preparedCaller memos metadata entered start ceiling ceiling uv handle scs value enteredPacket enteredReady
-      enteredStored enteredIncoming available closed dispatch currentFits currentKnown currentMass bucketBound
-      selectionMembers selectionLength (nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned)
-    have enlarged := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
-    have resources : OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling)
-        (finish uv outcome) := (certificate.mono enlarged.1 enlarged.2).post preparationPost
-    refine ⟨preparationFuel + branchFuel,
-      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)), outcome, ?_, resources⟩
-    intro extra
-    have atPreparation := preparationRun (branchFuel + extra)
-    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
-    rw [prepSame] at atPreparation
-    have rawAt := rawRun (preparationFuel + extra)
-    have continued := receiptRun (preparationFuel + extra)
-    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
-    rw [branchSame] at rawAt continued
-    have composed : SourcePruningEnumerationSharedReceiptContinuation.run
-        (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
-        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
-          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-          (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query) = outcome := by
-      rw [rawAt]
-      exact continued
-    have actual : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-          (preparationFuel + branchFuel + extra) edgesOf)
-        (hook (preparationFuel + branchFuel + extra)) checkEmpty
-        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-        (preparationFuel + branchFuel + extra) uv edgesOf caller before memos.query =
-      (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)),
-        some (SourcePruningEnumerationSharedReceiptContinuation.run
-          (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
-          (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
-            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
-            (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query))) := by
-      unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
-      rw [atPreparation]
-      cases value with
-      | node entry rows depth free =>
-          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
-            cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
-            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, here⟩).elim
-            | true => rfl
-          simp only [terminal, ↓reduceIte, frame, preparedCaller]
-      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
-          cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
-            simp only [here, Bool.false_eq_true, ↓reduceIte, frame, preparedCaller]
-    rw [composed] at actual
-    exact actual
-end ActualPreparedResources
-
```

### checked2607 to checked2487

```diff
--- checked2607.lean
+++ checked2487.lean
@@ -1 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueResources
@@ -2488,119 +2486,0 @@
-section ActualOpaqueResources
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem eager_opaque_resources
-    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
-      checkEmpty edgesOf stop order formulas solver recursiveDepth)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (ready : EnumerationDriver.Ready uv before.core)
-    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
-    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
-    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
-    (dispatch : (match (generalizing := false) value with
-      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
-    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
-    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
-    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
-    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
-    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
-      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
-        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
-        uv scs value caller before memos.query = some receipt) ∧
-      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
-        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
-          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
-          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
-      OutcomeResources formulas solver caller
-        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
-    := by
-  have cost : scs.length + 1 ≤ bound + 1 := by omega
-  obtain ⟨headFuel, receipt, reached, saved, final, next, headRun, headPost, headQuery,
-    _advanced, admitted, _pending, _history, headFits, headKnown, shape, _finalization⟩ :=
-    SourcePruningEnumerationSharedSelectedOpaqueDispatch.opaque_complete_resources seed formulas solver inventory
-      caller memos metadata before checkEmpty uv handle scs value packet ready stored incoming available closed
-      dispatch fits (reserved.1.prefix cost) known
-  have padding : Le (advance seed (scs.length + 1)).2 (advance seed (bound + 1)).2 ∧
-      (advance seed (scs.length + 1)).1 ⊆ (advance seed (bound + 1)).1 :=
-    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed cost,
-      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed cost⟩
-  have paddedFits := headFits.mono padding.1
-  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
-      reached.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
-  subst saved
-  rcases shape with completed | stopped | rejected
-  · obtain ⟨fragment, after, rfl, afterPacket, _counter, afterMass⟩ := completed
-    have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound := by omega
-    obtain ⟨callbackFuel, continued, callbackRun, resources⟩ :=
-      callback_eager_induction_resources holeKey keyMatches admits formulas solver next graph templates metadata uv
-        fragment reached final after checkEmpty edgesOf stop order recursiveDepth recursive
-        (advance seed (bound + 1)) (ceiling + bound) afterPacket admitted.2.2.1 paddedFits paddedKnown
-        selectionMembers selectionLength actualMass reserved.2
-    let folded : Fold := match continued with
-      | .complete outputs actual queries =>
-          .complete [.complete fragment reached final.query after] outputs actual queries
-      | .stopped outputs reason endpoint =>
-          .stopped [] outputs (.continuation (.complete fragment reached final.query after) reason endpoint)
-    have fullResources := resources.post headPost
-    have finished : OutcomeResources formulas solver caller
-        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed)
-        (finish uv folded) := by
-      cases continued <;>
-        simpa only [folded, finish, SourcePruningEnumerationSharedPreparedRecursive.endpoint,
-          OutcomeResources, fallbackPlan] using fullResources
-    refine ⟨headFuel + callbackFuel, .complete fragment reached final.query after, folded, ?_, ?_, finished⟩
-    · intro extra
-      have actual := headRun (callbackFuel + extra)
-      rw [← Nat.add_assoc] at actual
-      exact actual
-    · intro extra
-      have actual := callbackRun (headFuel + extra)
-      have common : callbackFuel + (headFuel + extra) = headFuel + callbackFuel + extra := by omega
-      rw [common] at actual
-      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual]
-      cases continued <;> rfl
-  · obtain ⟨after, outer, waiting, rfl, _counter, _mass⟩ := stopped
-    have resources : OutcomeResources (Typing := Typing) formulas solver caller (advance seed (bound + 1))
-        (.complete [] reached final.query) := by
-      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
-      intro output member
-      exact (List.not_mem_nil member).elim
-    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
-    refine ⟨headFuel, .stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after),
-      .complete [.stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after)] [] reached final.query,
-      headRun, ?_, ?_⟩
-    · intro extra
-      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
-        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
-    · simpa only [finish, fallbackPlan] using resources.mono growth.1 growth.2
-  · subst receipt
-    have resources : OutcomeResources (Typing := Typing) formulas solver caller (advance seed (bound + 1))
-        (.complete [] reached final.query) := by
-      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
-      intro output member
-      exact (List.not_mem_nil member).elim
-    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
-    have endpoints : (caller, memos.query) = (reached, final.query) := by
-      exact Option.some.inj _advanced
-    obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
-    refine ⟨headFuel, .rejected caller memos.query before,
-      .complete [.rejected caller memos.query before] [] caller memos.query, headRun, ?_, ?_⟩
-    · intro extra
-      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
-        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
-    · have fullResources := resources.mono growth.1 growth.2
-      simpa only [finish, fallbackPlan, callerSame, querySame] using fullResources
-
-end ActualOpaqueResources
-
```

```json
[
  {
    "from": "checked3093",
    "to": "failed3091",
    "from_sha256": "07219c234019081e7bcfe03d2c714eca723e0d7de3a7e7882272b2a2801b2de4",
    "to_sha256": "9f623c8b284a56d2596fd17f0c22d5e7b899bec9dbf618d299e8bcdd10b3367d",
    "patch_sha256": "9cb11b6053bbb1a60f019ff5fa404fd576e0f9d12b4396181c4e1e60eb37105e",
    "replayed_exact": true
  },
  {
    "from": "failed3091",
    "to": "checked2822",
    "from_sha256": "9f623c8b284a56d2596fd17f0c22d5e7b899bec9dbf618d299e8bcdd10b3367d",
    "to_sha256": "e53a8a310847e8e91be89f031748f4935c6740d7d30c27031f1c22fb71b150fb",
    "patch_sha256": "6517777255c93e40e68d8d13ae8c329984a524b1dc7064ce27f0bd1b7cc81f93",
    "replayed_exact": true
  },
  {
    "from": "checked2822",
    "to": "failed2821",
    "from_sha256": "e53a8a310847e8e91be89f031748f4935c6740d7d30c27031f1c22fb71b150fb",
    "to_sha256": "bbad00f5d3aeadb857e25b4e4b48b42126e41721d10b659a4f2a991dcaa1027e",
    "patch_sha256": "44018f2637465c468098063dc72b9301ea4127c054edc0dfb2e21e76b2ec70df",
    "replayed_exact": true
  },
  {
    "from": "failed2821",
    "to": "failed2819",
    "from_sha256": "bbad00f5d3aeadb857e25b4e4b48b42126e41721d10b659a4f2a991dcaa1027e",
    "to_sha256": "45d7c2b04cdd2b36fba510749d6db3547f5737c55f7e232915784c2b221512b9",
    "patch_sha256": "5771ae05931163c01e0afa545c576d1bee197c07fb8fb26971a992f60701a4a7",
    "replayed_exact": true
  },
  {
    "from": "failed2819",
    "to": "failed2817",
    "from_sha256": "45d7c2b04cdd2b36fba510749d6db3547f5737c55f7e232915784c2b221512b9",
    "to_sha256": "5fdb979ae8666644f8b8743275be19f7a93f06bb7f528998e74d35649e359ec5",
    "patch_sha256": "f432a02487ef1b58cf3484eef7efc1ac1ecf405eba270a988c7cf93b94dbeb70",
    "replayed_exact": true
  },
  {
    "from": "failed2817",
    "to": "failed2816",
    "from_sha256": "5fdb979ae8666644f8b8743275be19f7a93f06bb7f528998e74d35649e359ec5",
    "to_sha256": "10b4d69e70a3761cd47721f53d66849455fd3f21543deb7f88c326a196aa4098",
    "patch_sha256": "87f7409b32ae1dd9ff1cb4b87b5a83e51819621ddbea409e4e176adf7055f3e6",
    "replayed_exact": true
  },
  {
    "from": "failed2816",
    "to": "checked2607",
    "from_sha256": "10b4d69e70a3761cd47721f53d66849455fd3f21543deb7f88c326a196aa4098",
    "to_sha256": "2a22e0b2e012c358828766e1d5a472f822345d7fe80aeca38c8eafcefa512083",
    "patch_sha256": "70e9d19228e89450c55e9c09e30e1785714431100197b4d2ce8a5e413c0db158",
    "replayed_exact": true
  },
  {
    "from": "checked2607",
    "to": "checked2487",
    "from_sha256": "2a22e0b2e012c358828766e1d5a472f822345d7fe80aeca38c8eafcefa512083",
    "to_sha256": "e1f26f5a64b7d91af08065a837509e56d9d274c6eef849b10cc296631248055e",
    "patch_sha256": "82b15ff8fe0adea4762018c420b4f4621a25c56199986694ffd4b9c9f669ce1e",
    "replayed_exact": true
  }
]
```

## Frozen artifact: eager-resource-public-target-header.txt

SHA256 `01c37c9dabf7d093edb1741efeccf5c5d39378df0f7d76cfc7cf0883ea69b2fb`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
theorem runEager_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome
```

## Frozen artifact: private-eager-opaque-resources-header.txt

SHA256 `4270a8f265df76754f7c740a3f156224f04e0e059cfa49663d5197dbd7075196`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
private theorem eager_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
```

## Frozen artifact: private-eager-prepared-resources-header.txt

SHA256 `962387ab65fb44493770cc08d91b3ac6fd6634ed0556c18fcf68b74919f2593c`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
private theorem eager_prepared_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ ceiling)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling) :
    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
```

## Frozen artifact: private-eager-expansion-resources-header.txt

SHA256 `3b4c78aaecb0ebb5aebafd6bdc2c62d5ed8d828a31450c2e94606c2938e5df3d`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
private theorem eager_expansion_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome
```

## Frozen artifact: eager-cps-general-resources-stage-note.md

SHA256 `643df641ffde0fc5fda9d7d02cb82ca8e9c1975b5347634c2f31123030e108b5`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
# General actual eager resources at a fixed selected depth

Status at 2026-11-13 03:15 CET: UNCOMPILED candidate. ROOT is the sole compiler.
Frozen source: `eager-cps-general-resources-3091-9f623c8b.lean`. Lines:3091.
SHA256:`9f623c8b284a56d2596fd17f0c22d5e7b899bec9dbf618d299e8bcdd10b3367d`.
Basis: ROOT checked2822/e53a8a31 common preparation.
The candidate appends188 lines of actual prefix/depth-step proof and
77 lines of final induction and public wrapper.
The two explicit existing imports are SharedPrefixResources and PrefixMass.
The exact public20-line target01c37c9d is unchanged.
The private25-line step header3b4c78aa and9-line closure99acb9a1 are unchanged.
All prior snapshots and failed candidates remain unchanged.

The current prefix resource observation and PrefixValid observation apply
to the SAME actual selected prefix at one common sufficient work fuel.
The parked case derives the same current packet and Restart decision.
It places the lower-depth call at the computed fallback seed and mass.
Within-plan inclusion retains the final profile and guard alphabet.
The empty native branch retains its actual endpoint and no outputs.
The accepted narrowed branch supplies its actual Post/full Memos/query
and current preparation inputs to the checked common eager producer.

The depth induction discharges every PRIVATE lower-depth resume premise.
The terminal decisions use the literal unchanged operation.
The positive decision uses the actual selected-prefix step.
The public wrapper unfolds only the literal eager entry adapter.
There is no public child, callback, work, packet, model or capacity supplier.
Current Packet/Fits/Heap/selection/mass and computed eagerReserved remain.
Every actual emitted output, including stopped prefixes, retains the
ENTIRE existing OutcomeResources predicate and native/full-Memos endpoints.
All larger common work fuels must return the SAME actual outcome.

This candidate does not derive adequate original-source recursive depth.
It does not add general eager model or Program-role preservation.
It does not establish full Haskell default/lazy correspondence.
No new public resource law is claimed before ROOT compilation passes.

ROOT strict PASS at 2026-11-13 03:23 CET: checked3093 SHA07219c23.
The original3091 draft failed only closure computed-scalar normalization.
Two existing local opacity guards were added inside ActualEagerDepthClosure.
The public20-line header, all definitions and current assumptions are unchanged.
See general-eager-resources-final-handoff.md for the checked statement and limits.
```

## Frozen artifact: general-eager-resources-final-handoff.md

SHA256 `6a510ae46cd51bce08a796224196b13d5540e3a2270f752f5a06b2926be2e121`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
# General actual eager resource proof handoff

Updated:2026-11-13 03:25 CET.
ROOT strict compiler PASS at03:23 CET.
Checked source: `/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-cps-general-resources-3093.lean`.
Owner immutable copy: `eager-cps-general-resources-3093-07219c23.lean`.
SHA256:`07219c234019081e7bcfe03d2c714eca723e0d7de3a7e7882272b2a2801b2de4`. Lines:3093.
ROOT report: same checker path with `-checked.json` suffix.
Compiler exit0. Default200000 heartbeats. Max/high4GiB. Swap0.
Repository own/full/portable registration and publication remain ROOT work.
All old source snapshots remain unchanged.

The public law is `runEager_finite_complete_resources`.
Its exact original20-line header01c37c9d is unchanged.
For each fixed selected recursion depth, current Packet/Fits/Heap,
selector membership/count, suspended mass and computed eagerReserved
supply one common sufficient work fuel and one actual eager outcome.
Every larger common fuel returns that SAME complete or stopped outcome.
The ENTIRE existing OutcomeResources predicate holds at eagerFinal.
It retains the full native Post, inventory, full Memos/query identity,
physical guard heap and numeric bounds.
A returned endpoint is absent or is the same reached caller/query pair.
Every emitted output retains its full packet and resources.
This includes outputs emitted before a stopped prefix.
The proof executes the existing actual eager worker and continuations.
It adds no executable worker or altered native schedule.

The child proof inducts on actual ordinary height.
The same own-prefix receipt supplies strict child rank.
The ordered tuple calls the actual remaining tail after each child success.
The native heap and full memo state pass through every reached alternative.
Each sibling receives the same captured branch Core.
One actual finalizer and callback retain each captured receipt.
The common preparation derives current captured scalar/guard bounds.
The selected-prefix proof uses the same physical prefix at common fuel.
The parked branch uses actual Restart framing and computed fallback admission.
The outer Nat depth induction discharges the last private resume premise.
There is no public future child, callback, work, Packet, model or capacity provider.
Current computed eagerReserved remains an explicit arithmetic admission.

Source pins in the checked3093 file:

- `private theorem eager_child_height_complete`: checked source line1977.
- `private theorem finalize_child_inputs_packet`: checked source line2061.
- `private theorem eager_captured_resources`: checked source line2130.
- `private theorem eager_captured_rows_resources`: checked source line2343.
- `private theorem eager_opaque_resources`: checked source line2496.
- `private theorem eager_prepared_resources`: checked source line2618.
- `private theorem eager_expansion_resources`: checked source line2833.
- `private theorem eager_resume_complete`: checked source line3019.
- `theorem runEager_finite_complete_resources`: checked source line3064.

Local nodeReserved/nodePlan/headProfile opacity prevents unnecessary
computed-scalar normalization. Explicit successor unfolds retain the same
mathematical definitions. No heartbeat increase or linter suppression is used.

Open boundaries:

- Derive an adequate selected recursion depth from the original source input.
- Prove general eager ProgramSlots and fragment-role preservation.
- Prove general eager model preservation and required model existence.
- Attach the actual source readback without a second resource producer.
- Establish full default/lazy Haskell correspondence and all-alternative coverage.

The law permits real unsupported, rejected and depth-stopped outcomes.
It proves no output existence or complete search from these resource facts alone.
It proves no new Haskell defect or repair.
The existing source-width admission bridge uses the computed final plan.
It does not establish an unconditional fixed-machine-width claim.

Next work must use the checked3093 source as its immutable basis.
Do not import the live SharedEagerReservation module into copied whole-source candidates.
ROOT remains the sole compiler, Git publisher and root evidence/document owner.
```

## Frozen artifact: eager-opaque-resources-note.md

SHA256 `d8111c1b20984efe8ab2f33dfc4e6e10a412f2f7d07206ceb8e845de8afcabff`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
# Opaque eager resource composition

Status: uncompiled private draft. Root is the sole compiler.
Date: 2026-11-13 02:45 CET.

## Frozen files

- Fragment: eager-opaque-resources-fragment.lean.txt, 118 lines.
  SHA fcd88c8a6f8033154b37029911de448744159b3c5e1fe53247ce28f8e5ae05cd.
- Exact private eager_opaque_resources header: 35 lines.
  SHA 4270a8f265df76754f7c740a3f156224f04e0e059cfa49663d5197dbd7075196.
- Checked owner basis: eager-cps-finalize-child-inputs-stage.lean, 2121 lines.
  SHA 56fe353a is Root's verified prefix pin. The 805-line callback prefix
  supplies callback_eager_induction_resources without a new callback provider.

The section uses the existing SharedEagerReservation namespace and aliases.
Add the explicit existing import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueResources
at the top of the combined module. It is absent from the checked basis import closure.
No existing operation or theorem changes.

## Composition

1. Invoke SharedSelectedOpaqueDispatch.opaque_complete_resources ONCE.
   The original current Packet, Ready, stored slot, IncomingAvoid, available
   closed prepared value and actual dispatch equation supply its premises.
2. Restrict fallbackReserved's actual B+1 admission to scs.length+1.
   Pad the returned numeric profile and alphabet to advance seed (B+1)
   with advance_count_profile_mono and advance_count_alphabet_mono.
   Both compare positions of the SAME actual schedule using advance_add.
3. On completion, use the SAME returned Packet and Admitted fragment bound.
   The actual mass bound gives mass(after) <= ceiling+B. Invoke the checked
   callback_eager_induction_resources at that exact cache, caller and full Memos.
   The supplied recursive premise is the private concrete smaller-depth IH.
4. Compose the SAME original-to-reached Post with all callback OutcomeResources.
   Wrap its actual complete or stopped hook result in the literal receipt fold.
   Preserve stopped outputs, reasons and optional endpoint through finish.
5. For child rejection or stopped-empty receipts, use the literal continuation.
   It invokes no callback and emits no outputs. Retain the actual primitive Post,
   full Memos, numeric profile and alphabet. Pad only through eagerFinal_ge.
6. Align the primitive and callback fuel bounds by addition. Preserve the SAME
   chosen receipt and every larger-fuel raw run and receipt-continuation result.

The result uses exactly fallbackPlan B ceiling eagerFinal seed and fallbackReserved.
It does not invoke the old finite opaque producer, afterHead, finiteStep or its overplan.

## Boundary

This private composition preserves the entire OutcomeResources proposition.
It does not prove the smaller-depth IH or the outer prepared dispatch induction.
It adds no public resource, Packet, callback, model or after-state provider.
It supplies no assignment, source acceptance or output-existence theorem.
No compiler, repository, Git, Haskell or evidence operation was run.
```

## Frozen artifact: selected-preparation-backward-audit.md

SHA256 `3b1605cf280b0e508365f100e4d1dd15921640101a131ed8564e8620a067619b`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
# Backward meaning of the same selected preparation

Status: existing public law already supplies the required local implication.
Date: 2026-11-13 03:17 CET. No new theorem or resource-proof change is required.
The optional local usage fragment is uncompiled and adds zero public laws.

## Exact source pins

- SourcePruningEnumerationSelectedPreparationCurrent.lean:
  e2bf87c2d3e17ca17b491ab290d692a393ac828540196f9efdde579f0ac999bb.
- SourcePruningEnumerationSelectedPreparation.lean:
  333f85bea9383af9ed88932a5d26f3a8cf612a90ebaa6d34afe89caccb128def.
- SourcePruningEnumerationSelectedPreparationIdentification.lean:
  05aba8dcc3daf97258578f6af63449e755b7a1412a87767a5c843b7c9f635800.
- SourcePruningEnumerationSelectedValueCaller.lean:
  049742129acaa458ffb1e56df5e8b9c152267454a4208d96d245d19bf749c8e6.
- Frozen draft eager-cps-prepared-resources-2816-10b4d69e.lean:
  10b4d69e70a3761cd47721f53d66849455fd3f21543deb7f88c326a196aa4098.
  It extracts _meaning and _satisfaction at 2675. Its resource proof is unchanged.

## Existing exact fields

SelectedPreparation.complete_resources_current:30 retains, in ONE receipt:

- Actual run at every bound+extra: lines 45-46.
- SAME original-handle lookup, native Post, full memos and entered Packet: 47-51.
- Prepared result versus decoded value language equivalence: 58-60.
- WHOLE Satisfies equivalence across the two physical heaps and caches: 61-65.
- Input model implies prepared result meaning at assignment uv: 66-68.

The _satisfaction field is stronger than the required backward implication.
For arbitrary holds, ambient, residualMeaning and assignment, its first
projection says:

    Satisfies (handles holds ambient returnedHeap) residualMeaning assignment entered.core
      iff
    Satisfies (handles holds ambient inputCaller.heap) residualMeaning assignment before.core

Use (_satisfaction holds ambient residualMeaning assignment).1.mp.
Use .1.mpr for the reverse direction. Use .2 after the backward projection
to recover prepared result meaning at the SAME assignment uv.
_meaning alone is insufficient to restore the whole stored state.

SelectedValueCaller.advance:27 installs exactly returnedHeap. The prepared
caller's native machine heap is definitionally that heap. The caller keeps
its other tables. The producer's Post uses the SAME full memos, so its query
is still memos.query. Satisfies itself reads no query cache; no separate
query-model transport premise is needed.

## Why this is the actual preparation

The source builds the equivalence in SelectedPreparation.complete:118-124.
NativeLanguage.satisfies_keeps uses actual retained physical cells and the
actual entered PendingRealized receipt. The private satisfies_read lemma
then transports the SAME assignment through actual entry compression.
The producer uses one completed native preparation and its actual caller Post.

complete_resources_current:79-96 retains this receipt without strengthening
its semantic premises. It does not replace the returned heap or cache.
If only an actual all-larger-fuel run is available, existing identify_complete:28
returns these SAME fields. It identifies the observations at a common bound.
A new preparation evaluator or history relation is unnecessary.

## Exact local use and limits

private-preparation-backward-header.txt: 9 lines.
SHA a4876571e97f2ce3e62081a659f7c9a831c722f2c564cdc420e15f3442942c33.
selected-preparation-backward-usage.lean.txt: 10 lines.
SHA 170d6323e5d2fa4d56d80e3c041c9d895df545f113b43b6aff684408c26e08a2.
It uses the existing caller/before/entered/preparedCaller/_satisfaction bindings.
It is a local projection, not a new theorem with a supplied semantic gate.
No production or resource source was edited. No second producer was called.

The input here is the selected preparation input, which can follow narrowing.
This implication does not restore the state before that earlier prefix.
It does not restore the preparation input from an arbitrary later child/output.
Those steps still need actual shared/eager branch and boundary-retention history.
WHOLE structural discharge and canonical/final-arity conditions, when needed
by those later laws, do not follow from this local equivalence or noStop done.
The checked 74-line false-callback observer remains a separate local step.

All implications use a GIVEN assignment. They neither construct a satisfying
assignment nor show that an output has one. Full current source typing,
model existence and default-output correspondence remain separate obligations.
No compiler, Git, repository, evidence or Haskell operation was run.
```

## Frozen artifact: private-preparation-backward-header.txt

SHA256 `a4876571e97f2ce3e62081a659f7c9a831c722f2c564cdc420e15f3442942c33`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
have preparationBackward
    (holds : Constraint → Language.Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Language.Term Symbol → Prop)
    (assignment : Nat → Language.Term Symbol) :
    Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      preparedCaller.checked.native.machine.heap) residualMeaning assignment entered.core →
    Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      caller.checked.native.machine.heap) residualMeaning assignment before.core
```

## Frozen artifact: selected-preparation-backward-usage.lean.txt

SHA256 `170d6323e5d2fa4d56d80e3c041c9d895df545f113b43b6aff684408c26e08a2`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
have preparationBackward
    (holds : Constraint → Language.Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Language.Term Symbol → Prop)
    (assignment : Nat → Language.Term Symbol) :
    Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      preparedCaller.checked.native.machine.heap) residualMeaning assignment entered.core →
    Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      caller.checked.native.machine.heap) residualMeaning assignment before.core
    := (_satisfaction holds ambient residualMeaning assignment).1.mp
```

## Frozen artifact: child-inputs-program-slots-header.txt

SHA256 `a4ba0b9bde9d7d46087176aa93b8fbc6275b00b2464923144e7a90d2cde1391d`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
private theorem child_inputs_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing)
    (before after : Cached) (bucket : List Suspended) (fragment : Fragment) (queries : Queries)
    (safe : Safe before.core)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      original.checked.native.machine.heap before.core marked)
    (avoids : ∀ held, marked held → Avoids before.core.representatives held bucket)
    (actual : ChildInputs formulas solver original metadata before bucket fragment reached queries after) :
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      reached.checked.native.machine.heap after.core marked
```

## Frozen artifact: child-inputs-program-slots-fragment.lean

SHA256 `5f36e6c044311b6e3b3d1444484a1948354c14f6960cf70b1ac8a3666012108f`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
-- Insert in SharedEagerReservation after ChildInputs, before end ActualChildInputs.
-- Add the cycle-free import MicroCFTA.SourceSynthesisProgramRolesNativeHeap.
private theorem child_inputs_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing)
    (before after : Cached) (bucket : List Suspended) (fragment : Fragment) (queries : Queries)
    (safe : Safe before.core)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      original.checked.native.machine.heap before.core marked)
    (avoids : ∀ held, marked held → Avoids before.core.representatives held bucket)
    (actual : ChildInputs formulas solver original metadata before bucket fragment reached queries after) :
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      reached.checked.native.machine.heap after.core marked := by
  obtain ⟨_next, _final, post, _querySame, _packet, growth, _origin,
      protected, referenceEffect, _fragmentBound, _fragmentPending, _fragmentAvoid⟩ := actual
  have protects (held : Nat) (known : marked held) :
      EnumerationDriver.Protected held before.core after.core :=
    protected held (slots.bounded held known) (slots.roots held known) (avoids held known)
  have references (held : Nat) (known : marked held) :
      EnumerationReferences.ReferencesAllowed
        (fun target => ¬UnionFind.SameClass before.core.representatives held target) after.core :=
    referenceEffect _ (slots.incoming held known) (avoids held known)
      (EnumerationReferences.fresh_separate before.core safe held (slots.bounded held known))
  have carried := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
    original.checked.native.machine.heap reached.checked.native.machine.heap before.core marked
    post.effects.keeps slots
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro held known
    exact Nat.lt_of_lt_of_le (slots.bounded held known) growth
  · intro held known
    exact (protects held known).root
  · intro held known payload member sc listed same
    exact references held known payload member sc listed (((protects held known).classes sc.var).mp same)
  · intro held known
    obtain ⟨payload, stored, role⟩ := carried.stored held known
    exact ⟨payload, (protects held known).value.trans stored, role⟩
```

## Frozen artifact: next-eager-child-roles.md

SHA256 `4282deb24f2b39eb11f98bc5575edf1723b2a9edd3d08f5558cfb9be2039b83a`. This artifact describes its stated stage.
Earlier uncompiled/failed status remains historical. Final3093 is strictly checked.
The separate38-line ProgramSlots fragment remains UNCOMPILED in this packet.
The preparation semantic snippet is usage of an existing field, not a new law.

```text
# Next actual eager Program-role cut

Frozen source audit, 2026-11-13 03:21 CET. The new proof fragment is unverified.
Paths below are relative to lean/MicroCFTA/ unless stated otherwise.

## Smallest private lemma

child-inputs-program-slots-fragment.lean is 38 lines, SHA256:
5f36e6c044311b6e3b3d1444484a1948354c14f6960cf70b1ac8a3666012108f.
Its frozen 13-line header is child-inputs-program-slots-header.txt, SHA256:
a4ba0b9bde9d7d46087176aa93b8fbc6275b00b2464923144e7a90d2cde1391d.
PRIVATE child_inputs_program_slots takes only CURRENT Safe, ProgramSlots and
all-mark bucket Avoids plus the SAME successful ChildInputs. It concludes
ProgramSlots at that SAME reached caller/cache with the SAME marks. It changes
no resource contract, runs no producer, and supplies no desired after-role input.

Insert the fragment in SharedEagerReservation's defining module after ChildInputs,
before end ActualChildInputs. Its namespace is
MicroCFTA.SourcePruningEnumerationSharedEagerReservation. The private ChildInputs
name is available there. This is not a standalone importing module.
Add only import MicroCFTA.SourceSynthesisProgramRolesNativeHeap. A recursive import
check visited 2165 local modules and found no dependency on SharedEagerReservation.
The small role import therefore creates no cycle. No mangled private name is used.

## Why the current data suffices

SharedEagerReservation:913 ChildInputs already retains growth, full Post/Memos/query,
same-metadata Packet, protected roots/classes and future-allowed references.
Current bucket Avoids and slots.bounded/roots derive protection of each mark.
EnumerationReferences.fresh_separate:324 uses CURRENT Safe to discharge the
reference effect's future-variable condition. No future Safe is assumed.
ProgramRolesNativeHeap.keeps_program_slots:21 transports the old physical payload
roles with SAME Post.effects.keeps. Protected.value retains the raw slot value;
Protected.classes converts reference separation to the reached forest. Growth
and Protected.root finish ProgramSlots. This copies the logic of private
ChildTraversal.retained_slots:53, rather than replaying a child operation.
Protected.avoids, EnumerationDriver:51, also transports any untouched tail bucket.
It needs no fresh-mark bound because marks do not grow in this extraction.

## Successful fragment obligations remain open

This lemma preserves old slots. It does not derive FragmentRoles for the returned
fragment. ChildInputs does not mention incoming, source fields or a run equation.
A zero-child node can meet its fragment bound/pending/avoid conditions while
FragmentRoles rejects that whole Program layout. The abstract packet alone cannot
recover actual source-role semantics. This is not a runtime counterexample.

The next actual CPS role proof must follow the literal eagerChild execution.
For a Program demand, ValueFields permits empty or ordinary native values.
An empty input rejects; a node with annotation-only suspended paths is nonterminal.
SharedDriver.annotation_nonterminal:769 already contains that pure path argument.
Thus a successful Program-demanded ordinary child needs a height IH producing
concrete FragmentRoles at its ACTUAL done endpoint. Type children need no such
fragment clause and may use literal shallow fallback. Cover the syntactic
nondecreasing fallback; derive actual child decrease with prepared_child_lt:57.

At each selected row, own102 derives SAME old marks and actual child-bucket Avoids.
The ordered tuple must thread reached caller/cache/full queries and the current
roles, shift child indices, and derive Program roles only at full-field app2/3
and filter1. Count congruence51 allows a count-guarded success callback without
expanding TupleInputs. ParentCallbackRoles.fragment_roles_of_children:249 then
assembles the SAME full fragment list. Do not assemble a stopped prefix or supply
later tuple roles. Internal eager children do not finalize or record types.

## Failed branches, branch reset and outputs

Resource failure consumers retain Post/query for raw=[]; they promise no after
Packet or Safe. The new success lemma does not apply to that candidate. Preserve
previous emitted-output receipts, rather than asserting roles at every failure.
The sibling scan resets Core/cache to the captured before value. It threads the
ACTUAL reached native caller and Memos. Re-establish captured-cache roles with
native Keeps; do not reuse a prior sibling's completed cache or enlarged marks.
Likewise attach roles to each output's own caller heap/cache, not the final global
endpoint or a mark union across branches. Outer prefix/finalizer/callback and
restart induction must still establish their actual role receipts internally.

## Pins and scope

SharedDriver1859: 90b7611bfe4c131f59f287ed5f2a9ce0a3bf41bcc8f0e4754ba283a1a6e8a859.
SharedEagerChildren207: 029464163b7288a5ddbaae95996307fab7acec77e7f70e5a661db948757423eb.
SharedEagerReservation2487: e1f26f5a64b7d91af08065a837509e56d9d274c6eef849b10cc296631248055e.
The actual entry is SharedPreparedRecursiveChildPolicy.runEager:88. No separate
SharedEagerEnumeration module is present. Root reports checked private2822/e53a8a31;
Alpha owns later prefix/depth closure. The full public20 resource target remains
unproved. No eager role theorem, satisfying model, output existence or adequate
depth/whole enumeration completion is claimed. No compiler or repository edit ran.
```

## Reproduce

Current3093 is regular Lean source. Its own and compatibility packets check
all four public laws, exact source snapshots and standard axioms. The reverse
patches reconstruct all intermediate sources, including each failed draft.
Use the same serial4GiB cap and project Nix shell. No execution archive is
required. The unchanged original20-line target and full retained records are
part of the source. The old265776-byte Audit remains an exact prefix, followed
only by the new public theorem check and axiom check.
