import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
import MicroCFTA.SourcePruningEnumerationSharedFiniteSiblingResources
import MicroCFTA.SourcePruningEnumerationPrefixMass
import MicroCFTA.SourcePruningEnumerationSelectedEntry

/-!
# Actual shared expansion at a positive finite depth

The current prefix supplies its packet and its native endpoint.
Pure facts at that same prefix bound the retained suspended buckets.
Actual ordinary entry then runs the shared sibling scan and its callbacks.
Unsupported Mu, union and terminal-bucket entries retain their literal stop.
The smaller-depth hypothesis quantifies current packets. This composition
adds no future-state or successful-continuation premise.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open InternedProbeProvenance SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSelectedStep (runPrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "Forecast" => SourcePruningEnumerationSharedRecursiveReservation.final
local notation "stage" => SourcePruningEnumerationSharedRecursiveReservation.stage
local notation "RowResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "Ordinary" => SourcePruningEnumerationSharedSelectedContinuations.NativeOrdinaryContinuations.run
attribute [local irreducible] SourcePruningEnumerationSharedRecursiveReservation.step
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Typing Key : Type} {bits width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem entry_current
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core) :
    ∃ (fuel : Nat) (entered : Cached),
      (∀ extra, ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
        (fuel + extra) uv before.core) = [.ok ((uv, handle, scs, value), entered.core)]) ∧
      EnumerationExpandableIndex.frame entered.core before = entered ∧
      Packet formulas solver inventory caller memos metadata entered ∧
      EnumerationDriver.Ready uv entered.core ∧
      entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      EnumerationReferences.IncomingAvoid uv entered.core ∧ mass entered.core = mass before.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨fuel, actualValue, entered, entryRun, lookup, _available, _closed, counter, values,
    sameFlags, sameWaiting, enteredStored, enteredReady, _protected, enteredPaths, enteredRealized,
    enteredCounts, enteredFlags, _bucketBounded, _retained, stable⟩ :=
    SourcePruningEnumerationSelectedEntry.complete caller.checked.native.machine.heap before uv handle scs roots
      ready stored realized paths counts flags
  have same : actualValue = value := Option.some.inj (lookup.symm.trans decoded)
  subst actualValue
  have frame : EnumerationExpandableIndex.frame entered.core before = entered := by
    cases entered with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact sameFlags.symm
        · exact sameWaiting.symm
  have enteredPacket : Packet formulas solver inventory caller memos metadata entered := by
    obtain ⟨level, frontier, ordered⟩ := packet.ordered
    refine ⟨packet.context, stable.safe,
      EnumerationReferences.pending_read before.core entered.core stable packet.pending,
      ⟨roots, enteredPaths, stable.safe.1, enteredRealized, enteredCounts, enteredFlags⟩,
      ⟨level, frontier, EnumerationOrder.stratified_read before.core entered.core level frontier stable ordered⟩, ?_⟩
    simpa only [counter] using packet.bounded
  exact ⟨fuel, entered, entryRun, frame, enteredPacket, enteredReady, enteredStored,
    EnumerationReferences.incoming_read uv before.core entered.core stable incoming,
    SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core entered.core values⟩

variable [DecidableEq Symbol] [DecidableEq Node]

private theorem ordinary_current
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (ceiling : Nat) (initialMass : mass before.core ≤ ceiling) (inheritedLength : scs.length ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedRecursiveReservation.ScanReserved bits recursiveFuel seed ceiling ceiling
      (edgesOf (.node parentEntry storedEdges depth free)).length) :
    ∃ (bound : Nat) (raw : List (Except EnumerationState.Error
        ((Nat × Nat × List Suspended × Node) × EnumerationState.State Symbol Constraint)))
      (result : RowResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, Ordinary
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv edgesOf caller before memos.query = (raw, some result)) ∧
      OutcomeResources formulas solver caller
        (stage recursiveFuel seed ceiling ceiling (edgesOf (.node parentEntry storedEdges depth free)).length)
        (finish uv result) := by
  obtain ⟨entryFuel, entered, entryRun, frame, enteredPacket, enteredReady, enteredStored,
    enteredIncoming, sameMass⟩ := entry_current formulas solver inventory caller memos before metadata
      uv handle scs (.node parentEntry storedEdges depth free) packet ready stored decoded incoming
  obtain ⟨scanFuel, processed, outputs, afterCaller, next, final, result, scanRun, post,
    _captured, afterFits, afterKnown, _processedLength, _receipts, outputPackets, shape⟩ :=
    SourcePruningEnumerationSharedFiniteSiblingResources.alternatives_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed formulas solver recursive
      inventory caller memos entered uv handle scs parentEntry storedEdges
      (edgesOf (.node parentEntry storedEdges depth free)) depth free enteredPacket enteredReady enteredStored
      decoded (selectionMembers parentEntry storedEdges depth free) enteredIncoming bounded known
      selectionMembers selectionLength ceiling ceiling (by simpa only [sameMass] using initialMass)
      inheritedLength reserved
  have outputResources : ∀ output ∈ outputs, OutputResources formulas solver caller
      (stage recursiveFuel seed ceiling ceiling (edgesOf (.node parentEntry storedEdges depth free)).length) output := by
    intro output member
    obtain ⟨index, inside, certificate⟩ := outputPackets output member
    have own : OutputResources formulas solver caller (stage recursiveFuel seed ceiling ceiling (index + 1)) output :=
      certificate
    have growth := SourcePruningEnumerationSharedRecursiveReservation.count_mono recursiveFuel seed ceiling ceiling
      (by omega : index + 1 ≤ (edgesOf (.node parentEntry storedEdges depth free)).length)
    exact own.mono growth.1 growth.2
  have actualShape : result = .complete processed outputs afterCaller final.query ∨
      ∃ current, result = .stopped processed outputs current ∧
        (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) := by
    rcases shape with completed | ⟨current, stopped, reached, _certificate⟩
    · exact .inl completed
    · exact .inr ⟨current, stopped, reached⟩
  have certificate := finish_resources_general formulas solver caller uv
    (stage recursiveFuel seed ceiling ceiling (edgesOf (.node parentEntry storedEdges depth free)).length)
    processed outputs afterCaller next final result post afterFits afterKnown outputResources actualShape
  refine ⟨entryFuel + scanFuel, [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)],
    result, ?_, certificate⟩
  intro extra
  have atEntry := entryRun (scanFuel + extra)
  have entryCommon : entryFuel + (scanFuel + extra) = entryFuel + scanFuel + extra := by omega
  rw [entryCommon] at atEntry
  have atScan := scanRun (entryFuel + extra)
  have scanCommon : scanFuel + (entryFuel + extra) = entryFuel + scanFuel + extra := by omega
  rw [scanCommon] at atScan
  have actual := SourcePruningEnumerationSharedSelectedContinuations.NativeOrdinaryContinuations.entered
    (continueWith
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (entryFuel + scanFuel + extra) recursiveFuel)
      graph templates stop order (entryFuel + scanFuel + extra) metadata uv)
    checkEmpty (entryFuel + scanFuel + extra) (entryFuel + scanFuel + extra) (entryFuel + scanFuel + extra)
    (entryFuel + scanFuel + extra) (entryFuel + scanFuel + extra) uv uv handle scs parentEntry storedEdges depth free
    edgesOf caller before memos.query entered.core atEntry nonterminal
  rw [frame, atScan] at actual
  exact actual

/-- Current inputs and the smaller-depth hypothesis derive the literal shared positive expansion. -/
theorem expansion_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : mass before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedRecursiveReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (Forecast (recursiveFuel + 1) seed ceiling) outcome := by
  let start := SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed
  have finalGrowth := SourcePruningEnumerationSharedRecursiveReservation.final_ge (recursiveFuel + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedRecursiveReservation.narrowSeed_ge seed
  have stageGrowth := SourcePruningEnumerationSharedRecursiveReservation.stage_ge
    recursiveFuel start ceiling ceiling (SourcePruningEnumerationSharedRecursiveReservation.rows seed)
  obtain ⟨currentFuel, phases⟩ := checkpoint_resources holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  obtain ⟨legacyFuel, legacyComplete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet
  let prefixFuel := currentFuel + legacyFuel
  have shift (extra : Nat) : currentFuel + (legacyFuel + extra) = prefixFuel + extra := by
    dsimp only [prefixFuel]
    omega
  have legacy (extra : Nat) : SourcePruningEnumerationSelectedStep.PrefixValid
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + extra) uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query) := by
    have valid := legacyComplete (currentFuel + extra) uv chosen
    have common : legacyFuel + (currentFuel + extra) = prefixFuel + extra := by
      dsimp only [prefixFuel]
      omega
    simpa only [common] using valid
  rcases phases with ⟨checked, originalPhase⟩ | ⟨checked, heap, originalPhase⟩ |
    ⟨checked, phaseValue, heap, after, _nonempty, originalPhase⟩
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have valid := legacy 0
    rw [(phase 0).1] at valid
    have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet _ valid (phase 0).1
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
    · have certificate : OutcomeResources (Typing := Typing) formulas solver caller seed
          (.complete [] caller memos.query) := by
        refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_, certificate.mono finalGrowth.1 finalGrowth.2⟩
      intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [resume, observed]
    · let parkedSeed := SourcePruningEnumerationSharedRecursiveReservation.afterHead start ceiling
      let parkedMass := SourcePruningEnumerationRecursiveReservation.massCeil start ceiling ceiling
      have headGrowth := SourcePruningEnumerationSharedRecursiveReservation.afterHead_ge start ceiling
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : mass checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound reserved.first.2
      have growth := SourcePruningEnumerationSharedRecursiveReservation.first_le_final recursiveFuel seed ceiling
      have callbackResources : OutcomeResources formulas solver caller
          (SourcePruningEnumerationSharedRecursiveReservation.step recursiveFuel start ceiling ceiling) outcome := by
        simpa only [SourcePruningEnumerationSharedRecursiveReservation.step, parkedSeed, parkedMass] using resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, callbackResources.mono growth.1 growth.2⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [resume, observed]
      dsimp only
      rw [framed]
      exact actual
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have certificate : OutcomeResources (Typing := Typing) formulas solver caller start
        (.complete [] reached memos.query) := by
      refine ⟨reached, inventory, final, post, current.2.1, current.2.2, rfl, query.symm, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_⟩
    · intro extra
      rw [resume, (phase extra).1]
    · have padded := certificate.mono stageGrowth.1 stageGrowth.2
      simpa only [SourcePruningEnumerationSharedRecursiveReservation.final_succ] using padded
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨_action, prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      CurrentPrefixFacts.right_packet current.1
    have valid := legacy 0
    rw [prefixAt] at valid
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ valid
    obtain ⟨handle, scs, value, _oldMemos, _oldPost, _oldQuery, _oldPacket, ready, stored,
      decoded, available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      _oldFits, _oldKnown⟩ := admission
    have middleFits : Fits start.2 reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : mass after.core ≤ ceiling := Nat.le_trans
      (SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt)
      initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    by_cases ordinary : ∃ entry rows depth free,
        value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
    · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
      subst value
      have heapFits : SourceCurrentConstrainedCapRequiredResources.HeapFits start.2
          reached.checked.native.machine.heap := SourceCurrentConstrainedCapRequiredResources.of_checked middleFits
      have rowWidth := SourceCurrentConstrainedCapRequiredResources.node_width heapFits available
      have countBound : (edgesOf (.node entry rows depth free)).length ≤
          SourcePruningEnumerationSharedRecursiveReservation.rows seed :=
        Nat.le_trans (selectionLength entry rows depth free) (Nat.le_trans rowWidth (Nat.le_succ _))
      obtain ⟨scanFuel, raw, result, scanRun, certificate⟩ := ordinary_current
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start
        formulas solver recursive inventory reached middleMemos after uv handle scs entry rows depth free
        middlePacket ready stored decoded incoming nonterminal middleFits middleKnown selectionMembers selectionLength
        ceiling currentMass inheritedLength (reserved.ordinary _ countBound)
      have growth := SourcePruningEnumerationSharedRecursiveReservation.stage_le_final
        recursiveFuel seed ceiling (edgesOf (.node entry rows depth free)).length countBound
      refine ⟨prefixFuel + scanFuel, finish uv result, ?_, (certificate.mono growth.1 growth.2).post middlePost⟩
      intro extra
      obtain ⟨currentAction, currentPrefix, _current⟩ := phase (scanFuel + extra)
      have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
      rw [common] at currentPrefix
      have actual := scanRun (prefixFuel + extra)
      have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
      rw [scanCommon, middleQuery] at actual
      rw [resume, currentPrefix]
      dsimp only
      rw [actual]
    · have fallback : match value with
        | .node .. => scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
        | _ => True := by
        cases value with
        | node entry rows depth free =>
            change scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
            cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
            | true => rfl
        | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => trivial
      obtain ⟨entryFuel, entered, entryRun, _frame, _enteredPacket, _enteredReady, _enteredStored,
        _enteredIncoming, _sameMass⟩ := entry_current formulas solver inventory reached middleMemos after metadata
          uv handle scs value middlePacket ready stored decoded incoming
      let raw := [Except.ok (ε := EnumerationState.Error) ((uv, handle, scs, value), entered.core)]
      let outcome := SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult.stopped
        (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
        [] (.ordinary uv raw) (some (reached, memos.query))
      have certificate : OutcomeResources formulas solver reached start outcome := by
        refine ⟨reached, inventory, middleMemos, Post.refl middlePacket.context, middleFits, middleKnown,
          Or.inr ?_, fun _ member => (List.not_mem_nil member).elim⟩
        exact congrArg some (congrArg (Prod.mk reached) middleQuery.symm)
      refine ⟨prefixFuel + entryFuel, outcome, ?_, ?_⟩
      · intro extra
        obtain ⟨currentAction, currentPrefix, _current⟩ := phase (entryFuel + extra)
        have common : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [common] at currentPrefix
        have actualEntry := entryRun (prefixFuel + extra)
        have entryCommon : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [entryCommon] at actualEntry
        have actual : Ordinary
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (prefixFuel + entryFuel + extra) recursiveFuel) graph templates stop order
              (prefixFuel + entryFuel + extra) metadata uv)
            checkEmpty (prefixFuel + entryFuel + extra) (prefixFuel + entryFuel + extra)
              (prefixFuel + entryFuel + extra) (prefixFuel + entryFuel + extra) (prefixFuel + entryFuel + extra)
            uv edgesOf reached after memos.query = (raw, none) := by
          unfold SourcePruningEnumerationSharedSelectedContinuations.NativeOrdinaryContinuations.run
          rw [actualEntry]
          cases value with
          | node entry rows depth free =>
              simp only [fallback, ↓reduceIte]
              rfl
          | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => rfl
        rw [resume, currentPrefix]
        dsimp only
        rw [actual]
      · have padded := (certificate.mono stageGrowth.1 stageGrowth.2).post middlePost
        simpa only [SourcePruningEnumerationSharedRecursiveReservation.final_succ] using padded

end MicroCFTA.SourcePruningEnumerationSharedRecursive
