import MicroCFTA.SourcePruningEnumerationPrefixCheckpoint
import MicroCFTA.SourcePruningEnumerationParkedOneResources
import MicroCFTA.SourcePruningEnumerationOrdinaryFallbackResources
import MicroCFTA.SourcePruningEnumerationResumeExecution
import MicroCFTA.SourcePruningEnumerationFinishResources
import MicroCFTA.SourcePruningEnumerationExpansionAdmission

/-!
# One actual recursive expansion under an original reservation

The original packet supplies the selected prefix and its actual continuation.
One common work bound covers both stages. Parked, Empty and ordinary fallback
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
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourcePruningEnumerationSelectedStep (runPrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
local notation "narrowSeed" => SourcePruningEnumerationExpansionAdmission.narrowSeed
local notation "forecastCount" => SourcePruningEnumerationExpansionAdmission.count
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original current inputs derive a stable actual selected expansion at recursive depth one. -/
theorem selected_one_complete_resources
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
    (reserved : Reserved bits (narrowSeed seed) (forecastCount seed before.core))
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 1
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (reservationAdvance (narrowSeed seed) (forecastCount seed before.core)) outcome := by
  let start : Seed := (seed.1, headProfile seed.2)
  let inherited := SourcePruningEnumerationPrefixAdmission.suspendedBound before.core
  let count := SourcePruningEnumerationOriginalForecast.count start inherited
  let envelope := reservationAdvance start count
  change Reserved bits start count at reserved
  change ∃ bound outcome,
    (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 1
      metadata caller memos.query before (some (.expand uv)) = outcome) ∧
    OutcomeResources formulas solver caller envelope outcome
  have enlarged : Le seed.2 envelope.2 :=
    (headProfile_ge seed.2).trans (SourcePruningEnumerationIncomingReservation.advance_profile_ge start count)
  have retained : seed.1 ⊆ envelope.1 :=
    SourcePruningEnumerationIncomingReservation.advance_alphabet_ge start count
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
    obtain ⟨outcome, running, resources⟩ := parked_one_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
      caller memos before metadata prefixFuel uv checked seed packet bounded known phase
    exact ⟨prefixFuel, outcome, running, resources.mono enlarged retained⟩
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
      (SourcePruningEnumerationIncomingReservation.advance_profile_ge start count)
      (SourcePruningEnumerationIncomingReservation.advance_alphabet_ge start count)⟩
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
      obtain ⟨scanFuel, entered, processed, outputs, afterCaller, next, final, result, full,
        costBound, finalFits, finalKnown⟩ :=
        SourcePruningEnumerationNativeOrdinaryContinuations.ordinary_zero_complete_forecast
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          (seed.1, headProfile seed.2) inherited formulas solver inventory reached middleMemos after uv handle scs
          entry rows depth free middlePacket ready stored decoded (selectionMembers entry rows depth free)
          (selectionLength entry rows depth free) lengths incoming nonterminal middleFits reserved middleKnown
      obtain ⟨_entryRun, _stable, counter, _values, _sameFlags, _sameWaiting, _enteredPacket,
        outerRun, _scanRun, post, _captured, _afterFits, _afterKnown, _receipts, outputPackets, shape⟩ := full
      have outputResources : ∀ output ∈ outputs, OutputResources formulas solver reached envelope output := by
        intro output member
        obtain ⟨index, _inside, certificate⟩ := outputPackets output member
        exact OutputResources.of_outputAt formulas solver reached entered start scs
          (edgesOf (.node entry rows depth free)) index output count certificate
          (by simpa only [counter] using costBound)
      have certificate := finish_resources formulas solver reached entered uv start envelope scs
        (edgesOf (.node entry rows depth free)) processed outputs afterCaller next final result post
        finalFits finalKnown outputResources shape
      refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost⟩
      apply resume_one_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
        prefixFuel scanFuel uv metadata metadata caller reached memos.query memos.query before after
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
        (SourcePruningEnumerationIncomingReservation.advance_profile_ge start count)
        (SourcePruningEnumerationIncomingReservation.advance_alphabet_ge start count)).post middlePost⟩
      intro extra
      obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
      have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [samePrefix] at currentPrefix
      have actual := fallbackRun (prefixFuel + extra)
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (prefixFuel + entryFuel + extra) 0) graph templates stop order
          (prefixFuel + entryFuel + extra) metadata uv)
      have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
      rw [sameEntry, middleQuery] at actual
      rw [resume, currentPrefix]
      dsimp only
      rw [actual]

end MicroCFTA.SourcePruningEnumerationRecursive
