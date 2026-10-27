import MicroCFTA.SourcePruningEnumerationPrefixCheckpoint
import MicroCFTA.SourceFlatPruningRecursiveParkedResources
import MicroCFTA.SourcePruningEnumerationOrdinaryFallbackResources
import MicroCFTA.SourcePruningEnumerationResumeDepth
import MicroCFTA.SourceFlatPruningRecursiveOrdinaryForecastResources
import MicroCFTA.SourcePruningEnumerationFinishResources
import MicroCFTA.SourcePruningEnumerationExpansionAdmission

/-!
# Actual flat selected expansion at a positive finite depth

The original packet supplies one uniform prefix before the flat input is chosen.
Every related flat cache executes that prefix at the same work bound.
One original envelope pays the complete scan and its smaller-depth callbacks.
One common work bound covers all stages. Parked, Empty and ordinary fallback
routes retain their exact results. Each emitted output keeps its own native
endpoint, full memos, cache packet and resource bound.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile headProfile_ge)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationSelectedStep (runPrefix)
open SourcePruningEnumerationRecursive (Packet OutcomeResources)
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

/-- Original current inputs derive a stable actual selected expansion at a positive recursive depth. -/
theorem selected_finite_complete_resources
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
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (Forecast (recursiveFuel + 1) seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) (recursiveFuel + 1) metadata caller memos.query flat (some (.expand uv)) = flatOutcome ∧
          ResultRelated flatOutcome outcome := by
  rw [SourcePruningEnumerationFiniteReservation.final_succ]
  let start := SourcePruningEnumerationExpansionAdmission.narrowSeed seed
  let inherited := ceiling
  have stageGrowth := SourcePruningEnumerationFiniteReservation.stage_ge
    recursiveFuel start inherited inherited (SourcePruningEnumerationFiniteReservation.rows seed)
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
    obtain ⟨bound, outcome, running, resources, flatRunning⟩ := parked_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel recursive inventory
      caller memos before metadata prefixFuel uv checked seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved phase
    exact ⟨bound, outcome, running, by
      simpa only [SourcePruningEnumerationFiniteReservation.final_succ] using resources, flatRunning⟩
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
      rw [SourcePruningEnumerationRecursive.resume, (phase extra).1]
    · intro flat related extra
      have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
        holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
        (prefixFuel + extra) uv caller before flat memos related (phase extra).2
      rw [(phase extra).1] at replay
      obtain ⟨flatChecked, flatPrepared, observed⟩ :=
        SourceFlatPruningRecursivePrefixShape.rejected _ checked _ reached memos.query replay
      refine ⟨.complete [] reached memos.query, ?_, .nil, rfl, rfl⟩
      rw [resume, observed]
  · obtain ⟨checked, phaseValue, heap, after, _nonempty, phase⟩ := accepted
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨action, prefixAt, valid⟩ := phase 0
    rw [prefixAt] at valid
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
        _receipts, _outputPackets, _shape, _finished, _countBound, _finalFits, _finalKnown, certificate, flatRunning⟩ :=
        SourceFlatPruningNativeOrdinaryContinuations.ordinary_finite_complete_forecast
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start formulas solver recursive inventory
          reached middleMemos after uv handle scs entry rows depth free middlePacket ready stored decoded
          (selectionMembers entry rows depth free) incoming nonterminal middleFits middleKnown
          selectionMembers selectionLength inherited inherited currentMass inheritedBound reserved.scan
      refine ⟨prefixFuel + scanFuel, SourcePruningEnumerationRecursive.finish uv result, ?_,
        certificate.post middlePost, ?_⟩
      · apply SourcePruningEnumerationRecursive.resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
          prefixFuel scanFuel recursiveFuel uv metadata metadata caller reached memos.query memos.query before after
          [.ok ((uv, handle, scs, .node entry rows depth free), entered.core)] result
        · intro extra
          obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
          exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
        · intro extra
          simpa only [middleQuery] using outerRun extra
      · intro flat related extra
        let w := prefixFuel + scanFuel + extra
        obtain ⟨currentAction, currentPrefix, currentValid⟩ := phase (scanFuel + extra)
        have prefixSame : prefixFuel + (scanFuel + extra) = w := by dsimp [w]; omega
        rw [prefixSame] at currentPrefix currentValid
        have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
          holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
          w uv caller before flat memos related currentValid
        rw [currentPrefix] at replay
        obtain ⟨flatChecked, flatPrepared, actionCore, flatAfter, rightCore, observed, caches⟩ :=
          SourceFlatPruningRecursivePrefixShape.accepted _ checked _ reached memos.query after metadata replay
        obtain ⟨flatEntered, flatResult, actual, _enteredRelated, foldedRelated⟩ :=
          flatRunning flatAfter caches (prefixFuel + extra)
        have scanSame : scanFuel + (prefixFuel + extra) = w := by dsimp [w]; omega
        rw [scanSame, middleQuery] at actual
        refine ⟨finish uv flatResult, ?_, finish_related uv flatResult result foldedRelated⟩
        change resume holeKey fits admits graph templates checkEmpty edgesOf stop order w (recursiveFuel + 1)
          metadata caller memos.query flat (some (.expand uv)) = finish uv flatResult
        rw [resume, observed]
        dsimp only
        rw [actual]
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
      obtain ⟨entryFuel, entered, _entryRun, _stable, _counter, _values, _flags, _waiting,
        _enteredPacket, fallbackRun, _post, _fits, _known⟩ :=
        SourcePruningEnumerationNativeOrdinaryContinuations.fallback_complete_resources
          (Output := SourcePruningEnumerationRecursive.Output (bits + 2) Typing) (Reason := SourcePruningEnumerationRecursive.Failure (bits + 2) Typing)
          formulas solver inventory reached middleMemos after metadata uv handle scs value checkEmpty edgesOf
          middlePacket ready stored decoded (by cases value <;> exact fallback)
          (headProfile seed.2) (fun guard => guard ∈ seed.1)
          middleFits middleKnown
      let raw := [Except.ok (ε := EnumerationState.Error) ((uv, handle, scs, value), entered.core)]
      let outcome := SourcePruningEnumerationNativeContinuations.HookResult.stopped
        (Output := SourcePruningEnumerationRecursive.Output (bits + 2) Typing) (Reason := SourcePruningEnumerationRecursive.Failure (bits + 2) Typing)
        [] (.ordinary uv raw) (some (reached, memos.query))
      have certificate : OutcomeResources formulas solver reached start outcome := by
        refine ⟨reached, inventory, middleMemos, Post.refl middlePacket.context, middleFits, middleKnown,
          Or.inr ?_, fun _ member => False.elim (List.not_mem_nil member)⟩
        exact congrArg some (congrArg (Prod.mk reached) middleQuery.symm)
      refine ⟨prefixFuel + entryFuel, outcome, ?_, (certificate.mono
        stageGrowth.1 stageGrowth.2).post middlePost, ?_⟩
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
        have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [samePrefix] at currentPrefix
        have actual := fallbackRun (prefixFuel + extra)
          (SourcePruningEnumerationRecursive.continueWith (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (prefixFuel + entryFuel + extra) recursiveFuel) graph templates stop order
            (prefixFuel + entryFuel + extra) metadata uv)
        have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [sameEntry, middleQuery] at actual
        rw [SourcePruningEnumerationRecursive.resume, currentPrefix]
        dsimp only
        rw [actual]
      · intro flat related extra
        let w := prefixFuel + entryFuel + extra
        obtain ⟨currentAction, currentPrefix, currentValid⟩ := phase (entryFuel + extra)
        have samePrefix : prefixFuel + (entryFuel + extra) = w := by dsimp [w]; omega
        rw [samePrefix] at currentPrefix currentValid
        have replay := SourceFlatPruningSelectedPrefix.run_related_of_valid
          holeKey fits admits graph templates stop order metadata checkEmpty edgesOf formulas solver inventory
          w uv caller before flat memos related currentValid
        rw [currentPrefix] at replay
        obtain ⟨flatChecked, flatPrepared, actionCore, flatAfter, rightCore, observed, caches⟩ :=
          SourceFlatPruningRecursivePrefixShape.accepted _ checked _ reached memos.query after metadata replay
        have oldEntry := _entryRun (prefixFuel + extra)
        have sameEntry : entryFuel + (prefixFuel + extra) = w := by dsimp [w]; omega
        rw [sameEntry] at oldEntry
        obtain ⟨flatEntered, flatEntry, enteredRelated⟩ := SourceFlatPruningEntry.enter_replays
          reached.checked.native.machine.heap w uv flatAfter.core after.core
          (uv, handle, scs, value) entered.core caches.core oldEntry
        have flatFallback : ∀ (hook : Fragments.Fragment Symbol → Caller (bits + 2) →
            SourceEndpointMemo.Memos → EnumerationFlatCached.Cached Symbol Constraint →
            SourcePruningEnumerationNativeContinuations.HookResult
              (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
            SourceFlatPruningNativeOrdinaryContinuations.run hook
            checkEmpty w w w uv edgesOf reached flatAfter memos.query =
              ([.ok ((uv, handle, scs, value), flatEntered)], none) := by
          intro hook
          unfold SourceFlatPruningNativeOrdinaryContinuations.run
          rw [flatEntry]
          cases value with
          | node entry edges depth free => simp only [fallback, ↓reduceIte]
          | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => rfl
        let flatRaw := [Except.ok (ε := EnumerationState.Error) ((uv, handle, scs, value), flatEntered)]
        let flatOutcome := SourcePruningEnumerationNativeContinuations.HookResult.stopped
          (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          [] (.ordinary uv flatRaw) (some (reached, memos.query))
        refine ⟨flatOutcome, ?_, .nil, .ordinary uv (.cons (.ok _ enteredRelated) .nil), rfl⟩
        change resume holeKey fits admits graph templates checkEmpty edgesOf stop order w (recursiveFuel + 1)
          metadata caller memos.query flat (some (.expand uv)) = flatOutcome
        rw [resume, observed]
        dsimp only
        rw [flatFallback]

end MicroCFTA.SourceFlatPruningRecursive
