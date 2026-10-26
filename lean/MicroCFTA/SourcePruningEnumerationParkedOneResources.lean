import MicroCFTA.SourcePruningEnumerationPrefixCheckpoint
import MicroCFTA.SourcePruningEnumerationResumeZero
import MicroCFTA.SourcePruningEnumerationOutcomeResources
import MicroCFTA.SourcePruningEnumerationRecursivePrefix

/-!
# One parked expansion with native resources

The actual checked cache determines the restart observation. A blocked
restart rejects. Every other restart uses the exact zero-depth result.
The native caller and its resources do not change in this phase.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- The produced parked phase has one exact depth-one outcome at every larger work bound. -/
theorem parked_one_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (prefixFuel uv : Nat) (checked : Cached) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (phase : ∀ extra,
      SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query =
        .parked checked.core (some checked)
          (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core))) ∧
      SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + extra) uv caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
          (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query)) :
    ∃ outcome : Result,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (prefixFuel + extra) 1
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller seed outcome := by
  have valid := (phase 0).2
  rw [(phase 0).1] at valid
  have checkedPacket : Packet formulas solver inventory caller memos metadata checked :=
    prefix_packet holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid
  have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
    cases checked
    rfl
  by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
  · refine ⟨.complete [] caller memos.query, ?_, ?_⟩
    · intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
      rw [resume, observed]
    · refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
  · obtain ⟨outcome, stable, resources⟩ := resume_zero_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory caller memos
      checked metadata (SourcePruningEnumerationRestart.decision stop order metadata checked)
      seed.2 (fun guard => guard ∈ seed.1) checkedPacket bounded known
    refine ⟨outcome, ?_, ?_⟩
    · intro extra
      have observed := (phase extra).1
      rw [SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      rw [resume_parked holeKey fits admits graph templates checkEmpty edgesOf stop order
        (prefixFuel + extra) 0 metadata caller memos.query before uv checked.core checked.core checked metadata
        (SourcePruningEnumerationRestart.decision stop order metadata checked) observed, framed]
      exact stable (prefixFuel + extra)
    · refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, ?_⟩
      cases outcome with
      | complete outputs reached saved =>
          obtain ⟨callerSame, queriesSame, _bounded, _known, outputPackets⟩ := resources
          refine ⟨callerSame, queriesSame, ?_⟩
          intro output member
          obtain ⟨outputPacket, outputCaller, outputQueries, metadataSame, _cacheSame⟩ := outputPackets output member
          refine ⟨inventory, memos, metadata, ?_, outputQueries.symm, ?_, metadataSame, ?_, ?_⟩
          · simpa only [outputCaller] using Post.refl packet.context
          · simpa only [outputCaller] using outputPacket
          · simpa only [outputCaller] using bounded
          · simpa only [outputCaller] using known
      | stopped outputs reason endpoint =>
          obtain ⟨_selected, _nextSame, noOutputs, _reasonSame, endpointSame, _bounded, _known⟩ := resources
          refine ⟨Or.inr endpointSame, ?_⟩
          intro output member
          rw [noOutputs] at member
          exact False.elim (List.not_mem_nil member)

end MicroCFTA.SourcePruningEnumerationRecursive
