import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationPrefixPacket

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (fuel uv : Nat) (caller : Caller width) (memos : Memos) (before : Cached)

/-- Every retained prefix cache carries the recursive packet at its actual native endpoint. -/
theorem prefix_packet (packet : Packet formulas solver inventory caller memos metadata before)
    (observed : SourcePruningEnumerationSelectedStep.Result width Typing)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .parked _ (some after) _ => Packet formulas solver inventory caller memos metadata after
    | .narrowed _ _ reached queries _ (some after) _ _ =>
        ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          Packet formulas solver inventory reached final metadata after
    | _ => True := by
  have cached := SourcePruningEnumerationPrefixPacket.prefix_cache_valid holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed valid
  have native := SourcePruningEnumerationPrefixPacket.prefix_context holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed valid
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨cacheValid, safe, pending, counter, ordered⟩ := cached
          refine ⟨packet.context, safe, pending, cacheValid, ?_, ?_⟩
          · obtain ⟨level, frontier, initial⟩ := packet.ordered
            exact ⟨level, frontier, ordered level frontier initial⟩
          · simpa only [counter] using packet.bounded
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨cacheValid, safe, pending, counter, ordered⟩ := cached
          obtain ⟨final, post, saved⟩ := native
          refine ⟨final, post, saved, post.context, safe, pending, cacheValid, ?_, ?_⟩
          · obtain ⟨level, frontier, initial⟩ := packet.ordered
            exact ⟨level, frontier, ordered level frontier initial⟩
          · simpa only [counter] using packet.bounded

/-- A current packet derives one common prefix fuel for its actual expansion decision. -/
theorem packet_prefix_complete (packet : Packet formulas solver inventory caller memos metadata before) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (bound + extra) selected caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          selected caller before memos.query) := by
  cases chosen : SourcePruningEnumerationRestart.decision stop order metadata before with
  | none =>
      refine ⟨0, ?_⟩
      intro _extra selected picked
      cases picked
  | some next =>
      cases next with
      | done | stuck =>
          refine ⟨0, ?_⟩
          intro _extra selected picked
          cases picked
      | expand selected =>
          obtain ⟨bound, completed⟩ := SourcePruningEnumerationSelectedStep.restart_prefix_complete
            holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
            caller memos before selected packet.context packet.safe packet.pending packet.valid chosen
          refine ⟨bound, ?_⟩
          intro extra target picked
          have same := Option.some.inj picked
          cases same
          exact completed extra

end MicroCFTA.SourcePruningEnumerationRecursive
