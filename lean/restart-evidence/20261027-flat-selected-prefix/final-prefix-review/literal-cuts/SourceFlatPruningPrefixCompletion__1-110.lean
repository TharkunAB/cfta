import MicroCFTA.SourceFlatPruningSelectedPrefixReplay
import MicroCFTA.SourcePruningEnumerationRecursivePrefix

/-!
# Actual flat selected prefixes from the original recursive packet

The old producer supplies its complete universal packet once. Correspondence
and native index correctness concern each actual returned flat candidate.
The prefix does not execute ordinary siblings.
-/

namespace MicroCFTA.SourceFlatPruningSelectedPrefix

open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "OldCached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem correct_of_packet
    (related : EnumerationFlatCached.Related flat before)
    (packet : Packet formulas solver inventory caller memos metadata before) :
    EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap flat := by
  obtain ⟨roots, paths, storage, _realized, counts, flags⟩ := packet.valid
  exact EnumerationFlatNativeIndex.correct_of_related related caller.checked.native.machine.heap
    roots paths storage.aligned flags counts

variable [DecidableEq Symbol] [DecidableEq Node]

variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
variable (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (fuel uv : Nat) (caller : Caller width) (memos : Memos)
variable (before : OldCached)

private theorem related_packet
    (packet : Packet formulas solver inventory caller memos metadata before)
    (flatObserved : Result width Typing)
    (oldObserved : SourcePruningEnumerationSelectedStep.Result width Typing)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos oldObserved)
    (related : ResultRelated flatObserved oldObserved) :
    match (generalizing := false) flatObserved with
    | .parked _ (some after) _ =>
        ∃ oldAfter : OldCached, EnumerationFlatCached.Related after oldAfter ∧
          Packet formulas solver inventory caller memos metadata oldAfter ∧
          EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap after
    | .narrowed _ _ reached queries _ candidate _ =>
        ∃ final : Memos, Post formulas solver inventory caller reached final ∧
          final.query = queries ∧
          match (generalizing := false) candidate with
          | none => True
          | some after =>
              ∃ oldAfter : OldCached, EnumerationFlatCached.Related after oldAfter ∧
                Packet formulas solver inventory reached final metadata oldAfter ∧
                EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap after
    | _ => True := by
  have packets := SourcePruningEnumerationRecursive.prefix_packet holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller memos before
    packet oldObserved valid
  have native := SourcePruningEnumerationPrefixPacket.prefix_context holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos oldObserved valid
  cases flatObserved with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases oldObserved with
      | stopped _ _ => exact related.elim
      | narrowed _ _ _ _ _ _ _ _ => exact related.elim
      | parked oldChecked oldCandidate oldRaw =>
          cases candidate with
          | none => trivial
          | some after =>
              cases oldCandidate with
              | none => exact related.2.1.elim
              | some oldAfter =>
                  have caches : EnumerationFlatCached.Related after oldAfter := related.2.1
                  exact ⟨oldAfter, caches, packets, correct_of_packet caches packets⟩
  | narrowed checked prepared reached queries action candidate right =>
      cases oldObserved with
      | stopped _ _ => exact related.elim
      | parked _ _ _ => exact related.elim
      | narrowed oldChecked oldPrepared oldReached oldQueries oldAction oldCandidate oldRight ordinary =>
          obtain ⟨_checked, _prepared, callerSame, queriesSame, _action, writes, _right, _ordinary⟩ := related
          subst oldReached
          subst oldQueries
          cases candidate with
          | none =>
              obtain ⟨final, post, saved⟩ := native
              exact ⟨final, post, saved, trivial⟩
          | some after =>
              cases oldCandidate with
              | none => exact writes.elim
              | some oldAfter =>
                  obtain ⟨final, post, saved, returned⟩ := packets
                  exact ⟨final, post, saved, oldAfter, writes, returned,
                    correct_of_packet writes returned⟩
