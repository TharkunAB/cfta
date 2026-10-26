import MicroCFTA.SourcePruningEnumerationPrefixCheckpoint
import MicroCFTA.SourcePruningEnumerationParkedTwoResources
import MicroCFTA.SourcePruningEnumerationOrdinaryFallbackResources
import MicroCFTA.SourcePruningEnumerationResumeDepth
import MicroCFTA.SourcePruningEnumerationOrdinaryOneForecastResources
import MicroCFTA.SourcePruningEnumerationFinishResources
import MicroCFTA.SourcePruningEnumerationExpansionAdmission

/-!
# Two actual recursive expansions under an original reservation

The original packet supplies the selected prefix and its actual continuation.
One original envelope pays the complete scan and its depth-one callbacks.
One common work bound covers all stages. Parked, Empty and ordinary fallback
routes retain their exact results. Each emitted output keeps its own native
endpoint, full memos, cache packet and resource bound.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
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
local notation "Forecast" => SourcePruningEnumerationTwoExpansionForecast.final
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHook
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original current inputs derive a stable actual selected expansion at recursive depth two. -/
theorem selected_two_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : SourcePruningEnumerationTwoExpansionForecast.Reserved bits seed before.core)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 2
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (Forecast seed before.core) outcome := by
  let start := SourcePruningEnumerationTwoExpansionForecast.start seed
  let inherited := mass before.core
  have stageGrowth := SourcePruningEnumerationSiblingReservation.stage_ge
    start inherited inherited (SourcePruningEnumerationTwoExpansionForecast.rows seed)
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
    obtain ⟨bound, outcome, running, resources⟩ := parked_two_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
      caller memos before metadata prefixFuel uv checked seed packet bounded known
      selectionMembers selectionLength reserved phase
    exact ⟨bound, outcome, running, resources⟩
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
      stageGrowth.1 stageGrowth.2⟩
    intro extra
    rw [resume, (phase extra).1]
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
        SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt
      obtain ⟨scanFuel, entered, _processed, _outputs, _afterCaller, _next, _final, result,
        _entryRun, _stable, _counter, _values, _sameFlags, _sameWaiting, _enteredPacket,
        outerRun, _scanRun, _post, _captured, _afterFits, _afterKnown, _processedLength,
        _receipts, _outputPackets, _shape, _finished, _countBound, _finalFits, _finalKnown, certificate⟩ :=
        SourcePruningEnumerationNativeOrdinaryContinuations.ordinary_one_complete_forecast
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata start formulas solver inventory
          reached middleMemos after uv handle scs entry rows depth free middlePacket ready stored decoded
          (selectionMembers entry rows depth free) incoming nonterminal middleFits middleKnown
          selectionMembers selectionLength inherited inherited currentMass lengths reserved
      refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost⟩
      apply resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
        prefixFuel scanFuel 1 uv metadata metadata caller reached memos.query memos.query before after
        [.ok ((uv, handle, scs, .node entry rows depth free), entered.core)] result
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
        exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
      · intro extra
        simpa only [middleQuery] using outerRun extra
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
          (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          formulas solver inventory reached middleMemos after metadata uv handle scs value checkEmpty edgesOf
          middlePacket ready stored decoded (by cases value <;> exact fallback)
          (headProfile seed.2) (fun guard => guard ∈ seed.1)
          middleFits middleKnown
      let raw := [Except.ok (ε := EnumerationState.Error) ((uv, handle, scs, value), entered.core)]
      let outcome := SourcePruningEnumerationNativeContinuations.HookResult.stopped
        (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
        [] (.ordinary uv raw) (some (reached, memos.query))
      have certificate : OutcomeResources formulas solver reached start outcome := by
        refine ⟨reached, inventory, middleMemos, Post.refl middlePacket.context, middleFits, middleKnown,
          Or.inr ?_, fun _ member => False.elim (List.not_mem_nil member)⟩
        exact congrArg some (congrArg (Prod.mk reached) middleQuery.symm)
      refine ⟨prefixFuel + entryFuel, outcome, ?_, (certificate.mono
        stageGrowth.1 stageGrowth.2).post middlePost⟩
      intro extra
      obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
      have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [samePrefix] at currentPrefix
      have actual := fallbackRun (prefixFuel + extra)
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + entryFuel + extra) 1) graph templates stop order
          (prefixFuel + entryFuel + extra) metadata uv)
      have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [sameEntry, middleQuery] at actual
      rw [resume, currentPrefix]
      dsimp only
      rw [actual]

end MicroCFTA.SourcePruningEnumerationRecursive
