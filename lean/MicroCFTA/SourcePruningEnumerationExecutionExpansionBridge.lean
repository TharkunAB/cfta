import MicroCFTA.SourcePruningEnumerationFiniteExpansionResources
import MicroCFTA.SourcePruningEnumerationExecutionOrdinaryBridge
import MicroCFTA.SourcePruningEnumerationExecutionParkedBridge
import MicroCFTA.SourcePruningEnumerationPathSelectedPrefix
import MicroCFTA.SourcePruningEnumerationPreparedFiniteExpansionResources
import MicroCFTA.SourcePruningEnumerationExecutionSiblingBridge
import MicroCFTA.SourcePruningEnumerationExecutionOpaqueBridge
import MicroCFTA.SourcePruningEnumerationPathPreparedEntry

/-!
# Internal execution paths through both selected expansion workers

Each worker keeps its old stable outcome and resources.
The concrete smaller-depth path premise is internal to the eventual worker induction.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionExpansionBridge.Native
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile headProfile_ge)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationSelectedStep (runPrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Forecast" => SourcePruningEnumerationFiniteReservation.final
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
attribute [local irreducible] SourcePruningEnumerationFiniteReservation.step
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationRecursive
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationPathSelectedRaw (RawPaths SelectedPrefixPaths)
open SourcePruningEnumerationExecutionPaths (ResumeNative NativeStage)

/-- Original current inputs derive a stable actual selected expansion at a positive recursive depth. -/
theorem selected_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : mass before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (P : EqualityTrie.Path → Prop) (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (Forecast (recursiveFuel + 1) seed ceiling).1 P)
    (pathsIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2))
        (nextMemos : Memos) (nextCache : Cached) (nextMetadata : Metadata Typing)
        (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextCache →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      mass nextCache.core ≤ nextCeiling →
      SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel nextSeed nextCeiling →
      StatePaths P nextCache.core →
      ProjectionPaths (SourcePruningEnumerationFiniteReservation.final recursiveFuel nextSeed nextCeiling).1 P →
      ∃ bound, ∀ extra,
        SourcePruningEnumerationExecutionPaths.Native P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (Forecast (recursiveFuel + 1) seed ceiling) outcome ∧
      (∀ extra, ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) (recursiveFuel + 1) metadata caller memos.query before (some (.expand uv))) := by
  rw [SourcePruningEnumerationFiniteReservation.final_succ]
  let start := SourcePruningEnumerationExpansionAdmission.narrowSeed seed
  let inherited := ceiling
  have stageGrowth := SourcePruningEnumerationFiniteReservation.stage_ge
    recursiveFuel start inherited inherited (SourcePruningEnumerationFiniteReservation.rows seed)
  have stageProjected : ProjectionPaths
      (SourcePruningEnumerationFiniteReservation.stage recursiveFuel start inherited inherited
        (SourcePruningEnumerationFiniteReservation.rows seed)).1 P := by
    simpa only [SourcePruningEnumerationFiniteReservation.final_succ] using projected
  have prefixPaths (work : Nat) := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
    holeKey fits admits graph templates stop order metadata work work work work work work uv caller before memos.query original
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨prefixFuel, phases⟩ := SourcePruningEnumerationSelectedStep.prefix_checkpoint_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before (order metadata) uv roots packet.context packet.safe packet.pending selection
    realized paths counts flags
  rcases phases with parked | rejected | accepted
  · obtain ⟨checked, phase⟩ := parked
    obtain ⟨bound, outcome, running, resources, allPaths⟩ :=
      SourcePruningEnumerationExecutionParkedBridge.Native.parked_finite_complete_resources_paths
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel recursive inventory
      caller memos before metadata prefixFuel uv checked seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved phase P original projected pathsIH
    exact ⟨bound, outcome, running, by
      simpa only [SourcePruningEnumerationFiniteReservation.final_succ] using resources, allPaths⟩
  · obtain ⟨checked, heap, phase⟩ := rejected
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have valid := (phase 0).2
    rw [(phase 0).1] at valid
    have resources := SourcePruningEnumerationSelectedStep.prefix_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller before memos seed.2 (fun guard => guard ∈ seed.1)
      packet.context realized bounded known _ valid
    obtain ⟨final, post, query⟩ := SourcePruningEnumerationPrefixPacket.prefix_context
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller before memos _ valid
    have certificate : OutcomeResources (Typing := Typing) formulas solver caller start (.complete [] reached memos.query) :=
      ⟨reached, inventory, final, post, resources.1, resources.2, rfl, query.symm,
        fun _ member => False.elim (List.not_mem_nil member)⟩
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, certificate.mono
      stageGrowth.1 stageGrowth.2, ?_⟩
    · intro extra
      rw [resume, (phase extra).1]
    · intro extra
      refine ⟨original, ?_, prefixPaths (prefixFuel + extra), ?_⟩
      · rw [resume, (phase extra).1]
        intro output member
        exact False.elim (List.not_mem_nil member)
      · rw [(phase extra).1]
        trivial
  · obtain ⟨checked, phaseValue, heap, after, _nonempty, phase⟩ := accepted
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨action, prefixAt, valid⟩ := phase 0
    rw [prefixAt] at valid
    have retainedPaths := prefixPaths (prefixFuel + 0)
    rw [prefixAt] at retainedPaths
    have afterPaths : StatePaths P after.core := retainedPaths.2.2.1 after rfl
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ valid
    obtain ⟨handle, scs, value, middleMemos, middlePost, middleQuery, middlePacket, ready, stored,
      decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      middleFits, middleKnown⟩ := admission
    by_cases ordinary : ∃ entry rows depth free,
        value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
    · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
      subst value
      have currentMass : mass after.core ≤ inherited :=
        Nat.le_trans (SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt)
          initialMass
      have inheritedBound : scs.length ≤ inherited := Nat.le_trans lengths initialMass
      obtain ⟨scanFuel, entered, _processed, _outputs, _afterCaller, _next, _final, result,
        _entryRun, _stable, _counter, _values, _sameFlags, _sameWaiting, _enteredPacket,
        outerRun, _scanRun, _post, _captured, _afterFits, _afterKnown, _processedLength,
        _receipts, _outputPackets, _shape, _finished, countBound, _finalFits, _finalKnown, certificate⟩ :=
        SourcePruningEnumerationNativeOrdinaryContinuations.ordinary_finite_complete_forecast
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start formulas solver recursive inventory
          reached middleMemos after uv handle scs entry rows depth free middlePacket ready stored decoded
          (selectionMembers entry rows depth free) incoming nonterminal middleFits middleKnown
          selectionMembers selectionLength inherited inherited currentMass inheritedBound reserved.scan
      have scanProjected : ProjectionPaths
          (SourcePruningEnumerationFiniteReservation.stage recursiveFuel start inherited inherited
            (edgesOf (.node entry rows depth free)).length).1 P := by
        intro guard member
        exact stageProjected guard
          ((SourcePruningEnumerationFiniteReservation.count_mono recursiveFuel start inherited inherited countBound).2 member)
      obtain ⟨pathFuel, _pathEntered, _pathProcessed, _pathOutputs, _pathCaller, _pathInventory, _pathMemos,
        pathResult, _pathEntry, _pathStable, _pathCounter, _pathValues, _pathFlags, _pathWaiting,
        _pathPacket, pathOuter, _pathScan, _pathPost, _pathCaptured, _pathFits, _pathKnown,
        _pathLength, _pathReceipts, _pathOutputPackets, _pathShape, _pathFinished, stagePaths, outcomePaths⟩ :=
        SourcePruningEnumerationExecutionOrdinaryBridge.Native.ordinary_finite_complete_resources_paths
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start formulas solver recursive inventory
          reached middleMemos after uv handle scs entry rows depth free middlePacket ready stored decoded
          (selectionMembers entry rows depth free) incoming nonterminal middleFits middleKnown
          selectionMembers selectionLength inherited inherited currentMass inheritedBound
          (reserved.scan.prefix countBound) P afterPaths tails scanProjected pathsIH
      have running : ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + scanFuel + extra) (recursiveFuel + 1)
          metadata caller memos.query before (some (.expand uv)) = finish uv result := by
        apply resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
          prefixFuel scanFuel recursiveFuel uv metadata metadata caller reached memos.query memos.query before after
          [.ok ((uv, handle, scs, .node entry rows depth free), entered.core)] result
        · intro extra
          obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
          exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
        · intro extra
          simpa only [middleQuery] using outerRun extra
      refine ⟨prefixFuel + scanFuel + pathFuel, finish uv result, ?_, certificate.post middlePost, ?_⟩
      · intro extra
        simpa only [Nat.add_assoc] using running (pathFuel + extra)
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (scanFuel + pathFuel + extra)
        have prefixSame : prefixFuel + (scanFuel + pathFuel + extra) = prefixFuel + scanFuel + pathFuel + extra := by omega
        rw [prefixSame] at currentPrefix
        have outer := pathOuter (prefixFuel + scanFuel + extra)
        have stage := stagePaths (prefixFuel + scanFuel + extra)
        have common : pathFuel + (prefixFuel + scanFuel + extra) = prefixFuel + scanFuel + pathFuel + extra := by omega
        rw [common, middleQuery] at outer stage
        refine ⟨original, ?_, prefixPaths (prefixFuel + scanFuel + pathFuel + extra), ?_⟩
        · rw [resume, currentPrefix]
          dsimp only
          rw [outer]
          exact outcomePaths
        · rw [currentPrefix]
          exact stage
    · have fallback : match value with
        | .node .. => scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
        | _ => True := by
        cases value with
        | node entry rows depth free =>
            change scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
            cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact False.elim (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩)
            | true => rfl
        | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => trivial
      obtain ⟨entryFuel, entered, entryRun, _stable, _counter, _values, _flags, _waiting,
        _enteredPacket, fallbackRun, _post, _fits, _known⟩ :=
        SourcePruningEnumerationNativeOrdinaryContinuations.fallback_complete_resources
          (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          formulas solver inventory reached middleMemos after metadata uv handle scs value checkEmpty edgesOf
          middlePacket ready stored decoded (by cases value <;> exact fallback)
          (headProfile seed.2) (fun guard => guard ∈ seed.1)
          middleFits middleKnown
      have enteredPathsP : StatePaths P entered.core := by
        apply SourcePruningEnumerationPathPreparedEntry.enter_paths reached.checked.native.machine.heap
          entryFuel uv after.core entered.core (uv, handle, scs, value) afterPaths
        change Except.ok ((uv, handle, scs, value), entered.core) ∈
          ExceptT.run (SourcePruningEnumerationEntry.enter reached.checked.native.machine.heap entryFuel uv after.core)
        have actual := entryRun 0
        simp only [Nat.add_zero] at actual
        rw [actual]
        exact List.mem_singleton_self _
      let raw := [Except.ok (ε := EnumerationState.Error) ((uv, handle, scs, value), entered.core)]
      let outcome := SourcePruningEnumerationNativeContinuations.HookResult.stopped
        (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
        [] (.ordinary uv raw) (some (reached, memos.query))
      have rawPaths : RawPaths P raw := by
        intro result core member
        cases Except.ok.inj (List.mem_singleton.mp member)
        exact enteredPathsP
      have certificate : OutcomeResources formulas solver reached start outcome := by
        refine ⟨reached, inventory, middleMemos, Post.refl middlePacket.context, middleFits, middleKnown,
          Or.inr ?_, fun _ member => False.elim (List.not_mem_nil member)⟩
        exact congrArg some (congrArg (Prod.mk reached) middleQuery.symm)
      have running : ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + entryFuel + extra) (recursiveFuel + 1)
          metadata caller memos.query before (some (.expand uv)) = outcome := by
        intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
        have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [samePrefix] at currentPrefix
        have actual := fallbackRun (prefixFuel + extra)
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (prefixFuel + entryFuel + extra) recursiveFuel) graph templates stop order
            (prefixFuel + entryFuel + extra) metadata uv)
        have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [sameEntry, middleQuery] at actual
        rw [resume, currentPrefix]
        dsimp only
        rw [actual]
      refine ⟨prefixFuel + entryFuel, outcome, running,
        (certificate.mono stageGrowth.1 stageGrowth.2).post middlePost, ?_⟩
      intro extra
      obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
      have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [samePrefix] at currentPrefix
      have actual := fallbackRun (prefixFuel + extra)
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + entryFuel + extra) recursiveFuel) graph templates stop order
          (prefixFuel + entryFuel + extra) metadata uv)
      have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [sameEntry, middleQuery] at actual
      refine ⟨original, ?_, prefixPaths (prefixFuel + entryFuel + extra), ?_⟩
      · rw [running extra]
        exact ⟨(fun _ member => False.elim (List.not_mem_nil member)), rawPaths⟩
      · rw [currentPrefix]
        dsimp only
        unfold NativeStage
        rw [actual]
        refine ⟨rawPaths, ?_, ?_⟩
        · intro folded impossible
          cases impossible
        · cases value with
          | node entry rows depth free => simp only [fallback, ↓reduceIte]
          | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => trivial

end MicroCFTA.SourcePruningEnumerationExecutionExpansionBridge.Native

namespace MicroCFTA.SourcePruningEnumerationExecutionExpansionBridge.Prepared
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile headProfile_ge)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationSelectedStep (runPrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Forecast" => SourcePruningEnumerationPreparedReservation.final
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
attribute [local irreducible] SourcePruningEnumerationPreparedReservation.step
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
attribute [local irreducible] SourcePruningEnumerationSelectedValueCaller.normalizationProfile
attribute [local irreducible] SourcePruningEnumerationPreparedReservation.final
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationPreparedRecursive
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationPathSelectedRaw (RawPaths SelectedPrefixPaths)
open SourcePruningEnumerationExecutionPathData (FoldPaths PreparedFailurePaths)
open SourcePruningEnumerationExecutionPaths (ResumePrepared PreparedStage SiblingPaths)

/-- Original current inputs derive a stable actual selected expansion at a positive recursive depth. -/
theorem selected_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : mass before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (P : EqualityTrie.Path → Prop) (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (Forecast (recursiveFuel + 1) seed ceiling).1 P)
    (pathsIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2))
        (nextMemos : Memos) (nextCache : Cached) (nextMetadata : Metadata Typing)
        (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextCache →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      mass nextCache.core ≤ nextCeiling →
      SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel nextSeed nextCeiling →
      StatePaths P nextCache.core →
      ProjectionPaths (SourcePruningEnumerationPreparedReservation.final recursiveFuel nextSeed nextCeiling).1 P →
      ∃ bound, ∀ extra,
        SourcePruningEnumerationExecutionPaths.Prepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (Forecast (recursiveFuel + 1) seed ceiling) outcome ∧
      (∀ extra, ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) (recursiveFuel + 1) metadata caller memos.query before (some (.expand uv))) := by
  rw [SourcePruningEnumerationPreparedReservation.final_succ]
  let start := SourcePruningEnumerationPreparedReservation.preparedSeed seed
  let inherited := ceiling
  have stageGrowth := SourcePruningEnumerationPreparedReservation.stage_ge
    recursiveFuel start inherited inherited (SourcePruningEnumerationPreparedReservation.rows seed)
  have stageProjected : ProjectionPaths
      (SourcePruningEnumerationPreparedReservation.stage recursiveFuel start inherited inherited
        (SourcePruningEnumerationPreparedReservation.rows seed)).1 P := by
    simpa only [SourcePruningEnumerationPreparedReservation.final_succ] using projected
  have prefixPaths (work : Nat) := SourcePruningEnumerationPathSelectedPrefix.runPrefix_paths
    holeKey fits admits graph templates stop order metadata work work work work work work uv caller before memos.query original
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨prefixFuel, phases⟩ := SourcePruningEnumerationSelectedStep.prefix_checkpoint_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before (order metadata) uv roots packet.context packet.safe packet.pending selection
    realized paths counts flags
  rcases phases with parked | rejected | accepted
  · obtain ⟨checked, phase⟩ := parked
    obtain ⟨bound, outcome, running, resources, allPaths⟩ :=
      SourcePruningEnumerationExecutionParkedBridge.Prepared.parked_finite_complete_resources_paths
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel recursive inventory
      caller memos before metadata prefixFuel uv checked seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved phase P original projected pathsIH
    exact ⟨bound, outcome, running, by
      simpa only [SourcePruningEnumerationPreparedReservation.final_succ] using resources, allPaths⟩
  · obtain ⟨checked, heap, phase⟩ := rejected
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have valid := (phase 0).2
    rw [(phase 0).1] at valid
    have resources := SourcePruningEnumerationSelectedStep.prefix_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller before memos seed.2 (fun guard => guard ∈ seed.1)
      packet.context realized bounded known _ valid
    obtain ⟨final, post, query⟩ := SourcePruningEnumerationPrefixPacket.prefix_context
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller before memos _ valid
    have certificate : OutcomeResources (Typing := Typing) formulas solver caller
        (SourcePruningEnumerationExpansionAdmission.narrowSeed seed) (.complete [] reached memos.query) :=
      ⟨reached, inventory, final, post, resources.1, resources.2, rfl, query.symm,
        fun _ member => False.elim (List.not_mem_nil member)⟩
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, certificate.mono
      ((SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
        (SourcePruningEnumerationExpansionAdmission.narrowSeed seed).2).trans stageGrowth.1) stageGrowth.2, ?_⟩
    · intro extra
      rw [resume, (phase extra).1]
    · intro extra
      refine ⟨original, ?_, prefixPaths (prefixFuel + extra), ?_⟩
      · rw [resume, (phase extra).1]
        intro output member
        exact False.elim (List.not_mem_nil member)
      · rw [(phase extra).1]
        trivial
  · obtain ⟨checked, phaseValue, heap, after, _nonempty, phase⟩ := accepted
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨action, prefixAt, valid⟩ := phase 0
    rw [prefixAt] at valid
    have retainedPaths := prefixPaths (prefixFuel + 0)
    rw [prefixAt] at retainedPaths
    have afterPaths : StatePaths P after.core := retainedPaths.2.2.1 after rfl
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ valid
    obtain ⟨handle, scs, value, middleMemos, middlePost, middleQuery, middlePacket, ready, stored,
      decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      middleFits, middleKnown⟩ := admission
    have currentMass : mass after.core ≤ inherited :=
      Nat.le_trans (SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt)
        initialMass
    have inheritedBound : scs.length ≤ inherited := Nat.le_trans lengths initialMass
    obtain ⟨preparationFuel, preparedDecoded, preparedValue, preparedHeap, entered, retained, ordinary⟩ :=
      SourcePruningEnumerationPreparedNativeOrdinaryResources.complete_resources
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
        (SourcePruningEnumerationExpansionAdmission.narrowSeed seed) formulas solver recursive inventory
        reached middleMemos after uv handle scs middlePacket ready stored middleFits middleKnown incoming
        selectionMembers selectionLength inherited inherited currentMass inheritedBound reserved.scan
    obtain ⟨preparation, preparedKnown⟩ := retained
    obtain ⟨preparedPacket, preparedFits, _preparedMass⟩ := preparation
    obtain ⟨preparationRun, _preparedLookup, preparationPost, enteredPacket, stable,
      enteredReady, enteredStored, _enteredCounter, enteredValues, enteredFlags, enteredWaiting,
      preparedAvailable, preparedClosed, _preparedLanguage, _preparedModels⟩ := preparedPacket
    have enteredPathsP : StatePaths P entered.core := by
      apply SourcePruningEnumerationPathPreparedEntry.enter_paths reached.checked.native.machine.heap
        preparationFuel uv after.core entered.core (uv, handle, scs, preparedDecoded) afterPaths
      change Except.ok ((uv, handle, scs, preparedDecoded), entered.core) ∈
        ExceptT.run (SourcePruningEnumerationEntry.enter reached.checked.native.machine.heap preparationFuel uv after.core)
      have actual := congrArg Prod.fst (preparationRun 0)
      dsimp only [SourcePruningEnumerationSelectedPreparation.run] at actual
      simp only [Nat.add_zero] at actual
      rw [actual]
      exact List.mem_singleton_self _
    have framed : EnumerationExpandableIndex.frame entered.core after = entered := by
      cases entered with
      | mk core expandable waiting =>
          simp only [EnumerationExpandableIndex.frame] at *
          congr 1
          · exact enteredFlags.symm
          · exact enteredWaiting.symm
    have rawPaths : RawPaths P
        [.ok ((uv, handle, scs, preparedDecoded), entered.core)] := by
      intro result core member
      cases Except.ok.inj (List.mem_singleton.mp member)
      exact enteredPathsP
    have enteredMassP : mass entered.core ≤ inherited := by
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values after.core entered.core enteredValues]
      exact currentMass
    by_cases ordinaryShape : ∃ entry rows depth free,
        preparedValue = .node entry rows depth free ∧
          scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
    · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinaryShape
      obtain ⟨scanFuel, _processed, _outputs, _afterCaller, _next, _final, folded,
        _scanPacket, dispatchRun, _fullPost, resources⟩ := ordinary entry rows depth free same nonterminal
      have preparedHeapEq :
          (SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap).checked.native.machine.heap =
            preparedHeap := rfl
      have countBound := SourcePruningEnumerationPreparedReservation.selected_length_le seed
        (SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap) preparedFits
        entry rows (edgesOf (.node entry rows depth free)) depth free
        (by simpa only [preparedHeapEq, same] using preparedAvailable) (selectionLength entry rows depth free)
      have growth := SourcePruningEnumerationPreparedReservation.count_mono recursiveFuel start inherited inherited countBound
      have scanProjected : ProjectionPaths
          (SourcePruningEnumerationPreparedReservation.stage recursiveFuel start inherited inherited
            (edgesOf (.node entry rows depth free)).length).1 P := by
        intro guard member
        exact stageProjected guard (growth.2 member)
      obtain ⟨pathFuel, _pathProcessed, _pathOutputs, _pathCaller, _pathInventory, _pathMemos,
        pathResult, scanAt, _pathPost, _pathPacket, _pathFits, _pathKnown, _pathLength,
        _pathReceipts, _pathOutputsAt, _pathShape, foldPaths, invocations⟩ :=
        SourcePruningEnumerationExecutionSiblingBridge.Prepared.alternatives_finite_complete_resources_paths
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start formulas solver recursive inventory
          (SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap) middleMemos entered
          uv handle scs entry rows (edgesOf (.node entry rows depth free)) depth free
          enteredPacket enteredReady enteredStored
          (by simpa only [preparedHeapEq, same] using preparedAvailable)
          (by simpa only [same, Value.free] using preparedClosed) (selectionMembers entry rows depth free)
          (EnumerationReferences.incoming_read uv after.core entered.core stable incoming)
          preparedFits preparedKnown selectionMembers selectionLength inherited inherited enteredMassP inheritedBound
          (reserved.scan.prefix countBound) P enteredPathsP tails scanProjected pathsIH
      have dispatchPathsAt (extra : Nat) : SourcePruningEnumerationSelectedContinuations.run
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (preparationFuel + pathFuel + extra) recursiveFuel)
            graph templates stop order (preparationFuel + pathFuel + extra) metadata uv)
          checkEmpty (preparationFuel + pathFuel + extra) (preparationFuel + pathFuel + extra)
          (preparationFuel + pathFuel + extra) (preparationFuel + pathFuel + extra)
          (preparationFuel + pathFuel + extra) (preparationFuel + pathFuel + extra)
          (preparationFuel + pathFuel + extra) uv edgesOf reached after middleMemos.query =
            (([.ok ((uv, handle, scs, preparedDecoded), entered.core)],
              some (.done (.node entry rows depth free) preparedHeap)), some pathResult) := by
        have preparationAt : SourcePruningEnumerationSelectedPreparation.run
            (preparationFuel + pathFuel + extra) (preparationFuel + pathFuel + extra) uv reached after =
              ([.ok ((uv, handle, scs, preparedDecoded), entered.core)],
                some (.done (.node entry rows depth free) preparedHeap)) := by
          simpa only [Nat.add_assoc, same] using preparationRun (pathFuel + extra)
        have actual := SourcePruningEnumerationSelectedContinuations.ordinary
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (preparationFuel + pathFuel + extra) recursiveFuel)
            graph templates stop order (preparationFuel + pathFuel + extra) metadata uv)
          checkEmpty (preparationFuel + pathFuel + extra) (preparationFuel + pathFuel + extra)
          (preparationFuel + pathFuel + extra) (preparationFuel + pathFuel + extra)
          (preparationFuel + pathFuel + extra) (preparationFuel + pathFuel + extra)
          (preparationFuel + pathFuel + extra) uv uv handle scs preparedDecoded entry rows depth free
          preparedHeap entered.core edgesOf reached after middleMemos.query preparationAt nonterminal
        have scan := scanAt (preparationFuel + extra)
        have common : pathFuel + (preparationFuel + extra) = preparationFuel + pathFuel + extra := by omega
        rw [common] at scan
        rw [framed, scan] at actual
        exact actual
      have running : ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + (preparationFuel + scanFuel) + extra) (recursiveFuel + 1)
          metadata caller memos.query before (some (.expand uv)) = finish uv folded := by
        apply resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
          prefixFuel (preparationFuel + scanFuel) recursiveFuel uv metadata metadata caller reached
          memos.query memos.query before after
          ([.ok ((uv, handle, scs, preparedDecoded), entered.core)],
            some (.done (.node entry rows depth free) preparedHeap)) folded
        · intro extra
          obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
          exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
        · intro extra
          simpa only [middleQuery] using dispatchRun extra
      refine ⟨prefixFuel + (preparationFuel + scanFuel) + pathFuel, finish uv folded, ?_,
        (resources.mono growth.1 growth.2).post middlePost, ?_⟩
      · intro extra
        simpa only [Nat.add_assoc] using running (pathFuel + extra)
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (preparationFuel + scanFuel + pathFuel + extra)
        have samePrefix : prefixFuel + (preparationFuel + scanFuel + pathFuel + extra) =
            prefixFuel + (preparationFuel + scanFuel) + pathFuel + extra := by omega
        rw [samePrefix] at currentPrefix
        have dispatch := dispatchPathsAt (prefixFuel + scanFuel + extra)
        have sameDispatch : preparationFuel + pathFuel + (prefixFuel + scanFuel + extra) =
            prefixFuel + (preparationFuel + scanFuel) + pathFuel + extra := by omega
        rw [sameDispatch, middleQuery] at dispatch
        have scan := scanAt (prefixFuel + preparationFuel + scanFuel + extra)
        have currentInvocations := invocations (prefixFuel + preparationFuel + scanFuel + extra)
        have sameScan : pathFuel + (prefixFuel + preparationFuel + scanFuel + extra) =
            prefixFuel + (preparationFuel + scanFuel) + pathFuel + extra := by omega
        rw [sameScan, middleQuery] at scan currentInvocations
        refine ⟨original, ?_, prefixPaths (prefixFuel + (preparationFuel + scanFuel) + pathFuel + extra), ?_⟩
        · rw [resume, currentPrefix]
          dsimp only
          rw [dispatch]
          exact SourcePruningEnumerationExecutionPathData.prepared_finish_paths uv pathResult foldPaths
        · rw [currentPrefix]
          dsimp only
          unfold PreparedStage
          rw [dispatch]
          dsimp only
          refine ⟨rawPaths, ?_, ?_⟩
          · intro result found
            cases Option.some.inj found
            exact foldPaths
          · rw [nonterminal, framed]
            unfold SiblingPaths
            refine ⟨?_, currentInvocations⟩
            rw [scan]
            exact foldPaths
    · have dispatchGate : (match (generalizing := false) preparedValue with
          | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
          | _ => false) = false := by
        cases preparedValue with
        | node entry rows depth free =>
            cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact False.elim (ordinaryShape ⟨entry, rows, depth, free, rfl, terminal⟩)
            | true => rfl
        | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => rfl
      have enteredMass : mass entered.core ≤ inherited := by
        rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values after.core entered.core enteredValues]
        exact currentMass
      have opaqueProjected : ProjectionPaths
          (SourcePruningEnumerationPreparedReservation.step recursiveFuel start inherited inherited).1 P := by
        intro guard member
        exact projected guard
          ((SourcePruningEnumerationPreparedReservation.first_le_final recursiveFuel seed ceiling).2 member)
      obtain ⟨opaqueFuel, _receipt, _middleCaller, _saved, _middleMemos, _middleInventory, _outcome, folded,
        _headRun, _headPost, _headQuery, _advanced, _admitted, _pending, _history, _headFits, _headKnown,
        _shape, _paddedFits, _paddedKnown, _callbackRun, _receiptRun, resources, opaqueFoldRun, opaquePaths, finishedPaths⟩ :=
        SourcePruningEnumerationExecutionOpaqueBridge.Prepared.opaque_finite_complete_resources_paths
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
          start formulas solver recursive inventory
          (SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap) middleMemos entered
          uv handle scs preparedValue enteredPacket enteredReady enteredStored
          (EnumerationReferences.incoming_read uv after.core entered.core stable incoming)
          preparedAvailable preparedClosed dispatchGate preparedFits preparedKnown selectionMembers selectionLength
          inherited inherited enteredMass inheritedBound reserved.first P enteredPathsP opaqueProjected pathsIH
      have growth := SourcePruningEnumerationPreparedReservation.first_le_final recursiveFuel seed ceiling
      have padded : OutcomeResources formulas solver
          (SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap)
          (Forecast (recursiveFuel + 1) seed ceiling) (finish uv folded) :=
        resources.mono growth.1 growth.2
      have originalResources := (padded.post preparationPost).post middlePost
      have dispatchEquation (extra : Nat) : SourcePruningEnumerationSelectedContinuations.run
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (preparationFuel + opaqueFuel + extra) recursiveFuel)
            graph templates stop order (preparationFuel + opaqueFuel + extra) metadata uv)
          checkEmpty (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
          (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
          (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
          (preparationFuel + opaqueFuel + extra) uv edgesOf reached after middleMemos.query =
            (([.ok ((uv, handle, scs, preparedDecoded), entered.core)], some (.done preparedValue preparedHeap)), some folded) := by
        have preparationAt : SourcePruningEnumerationSelectedPreparation.run
            (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra) uv reached after =
              ([.ok ((uv, handle, scs, preparedDecoded), entered.core)], some (.done preparedValue preparedHeap)) := by
          simpa only [Nat.add_assoc] using preparationRun (opaqueFuel + extra)
        have foldAt := opaqueFoldRun (preparationFuel + extra)
        have common : opaqueFuel + (preparationFuel + extra) = preparationFuel + opaqueFuel + extra := by omega
        rw [common] at foldAt
        have dispatchAt : SourcePruningEnumerationSelectedContinuations.run
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                (preparationFuel + opaqueFuel + extra) recursiveFuel)
              graph templates stop order (preparationFuel + opaqueFuel + extra) metadata uv)
            checkEmpty (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
            (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
            (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
            (preparationFuel + opaqueFuel + extra) uv edgesOf reached after middleMemos.query =
              (([.ok ((uv, handle, scs, preparedDecoded), entered.core)], some (.done preparedValue preparedHeap)), some folded) := by
          cases preparedValue with
          | node entry rows depth free =>
              have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
                cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
                | false => exact False.elim (ordinaryShape ⟨entry, rows, depth, free, rfl, terminal⟩)
                | true => rfl
              have observed := SourcePruningEnumerationSelectedContinuations.terminal
                (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                    (preparationFuel + opaqueFuel + extra) recursiveFuel)
                  graph templates stop order (preparationFuel + opaqueFuel + extra) metadata uv)
                checkEmpty (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
                (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
                (preparationFuel + opaqueFuel + extra) (preparationFuel + opaqueFuel + extra)
                (preparationFuel + opaqueFuel + extra) uv uv handle scs preparedDecoded
                (.node entry rows depth free) preparedHeap entered.core edgesOf reached after middleMemos.query
                preparationAt terminal
              rw [framed, foldAt] at observed
              exact observed
          | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
              simp only [SourcePruningEnumerationSelectedContinuations.run, preparationAt, framed, ite_self]
              rw [foldAt]
        exact dispatchAt
      have running : ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + (preparationFuel + opaqueFuel) + extra) (recursiveFuel + 1)
          metadata caller memos.query before (some (.expand uv)) = finish uv folded := by
        apply resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
          prefixFuel (preparationFuel + opaqueFuel) recursiveFuel uv metadata metadata caller reached
          memos.query memos.query before after
          ([.ok ((uv, handle, scs, preparedDecoded), entered.core)], some (.done preparedValue preparedHeap)) folded
        · intro extra
          obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
          exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
        · intro extra
          simpa only [middleQuery] using dispatchEquation extra
      refine ⟨prefixFuel + (preparationFuel + opaqueFuel), finish uv folded, running, ?_, ?_⟩
      · simpa only [SourcePruningEnumerationPreparedReservation.final_succ] using originalResources
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (preparationFuel + opaqueFuel + extra)
        have samePrefix : prefixFuel + (preparationFuel + opaqueFuel + extra) =
            prefixFuel + (preparationFuel + opaqueFuel) + extra := by omega
        rw [samePrefix] at currentPrefix
        have dispatch := dispatchEquation (prefixFuel + extra)
        have sameDispatch : preparationFuel + opaqueFuel + (prefixFuel + extra) =
            prefixFuel + (preparationFuel + opaqueFuel) + extra := by omega
        rw [sameDispatch, middleQuery] at dispatch
        have currentOpaque := opaquePaths (prefixFuel + preparationFuel + extra)
        have currentFold := opaqueFoldRun (prefixFuel + preparationFuel + extra)
        have sameOpaque : opaqueFuel + (prefixFuel + preparationFuel + extra) =
            prefixFuel + (preparationFuel + opaqueFuel) + extra := by omega
        rw [sameOpaque, middleQuery] at currentOpaque currentFold
        have foldPaths := currentOpaque.2.1
        rw [currentFold] at foldPaths
        refine ⟨original, ?_, prefixPaths (prefixFuel + (preparationFuel + opaqueFuel) + extra), ?_⟩
        · rw [resume, currentPrefix]
          dsimp only
          rw [dispatch]
          exact finishedPaths
        · rw [currentPrefix]
          dsimp only
          unfold PreparedStage
          rw [dispatch]
          dsimp only
          refine ⟨rawPaths, ?_, ?_⟩
          · intro result found
            cases Option.some.inj found
            exact foldPaths
          · rw [framed]
            cases preparedValue with
            | node entry rows depth free =>
                have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
                  cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
                  | false => exact False.elim (ordinaryShape ⟨entry, rows, depth, free, rfl, terminal⟩)
                  | true => rfl
                rw [terminal]
                exact currentOpaque
            | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;> exact currentOpaque

end MicroCFTA.SourcePruningEnumerationExecutionExpansionBridge.Prepared
