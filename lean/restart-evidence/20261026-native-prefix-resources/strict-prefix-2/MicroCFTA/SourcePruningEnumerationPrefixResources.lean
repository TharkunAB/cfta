import MicroCFTA.SourcePruningNativeViewResources
import MicroCFTA.SourcePruningEnumerationRecursivePrefix

/-!
# Original resources at actual selected-prefix callers

The prefix retains the full earlier validity certificate. Its actual narrowing
endpoint fits the initial read and rebuild forecast. The original guard
predicate stays valid. The recursive worker does not execute the finish
expression used in the earlier certificate.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile headProfile_ge)
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

/-- Bound the actual native endpoint of the selected prefix. -/
def Resources (profile : Profile) (property : Constraint → Prop) (caller : Caller width) :
    Result width Typing → Prop
  | .narrowed _ _ reached _ _ _ _ _ =>
      Fits (headProfile profile) reached.checked ∧ Heap property reached.checked.native.machine.heap
  | _ => Fits (headProfile profile) caller.checked ∧ Heap property caller.checked.native.machine.heap

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (r n p h k uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf r n p h k uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf r n p h k uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩

variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)

/-- The earlier prefix certificate bounds the same caller, including Empty rejection. -/
theorem prefix_resources (profile : Profile) (property : Constraint → Prop)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap)
    (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    Resources profile property caller observed := by
  have full := valid.2.1
  cases observed with
  | stopped _ _ | parked _ _ _ => exact ⟨bounded.mono (headProfile_ge profile), known⟩
  | narrowed checked prepared reached queries action candidate right ordinary =>
      obtain ⟨_next, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
        (.narrowed checked prepared reached queries action candidate right ordinary)
      rw [finished] at full
      obtain ⟨oldHandle, scs, readAfter, reading, _checking, oldValue, value, heap,
        _selectedAction, _final, decoded, narrowed, _prepared, _samePrepared, reachedAt,
        _queries, _post, _saved, _shape⟩ := full
      have readSuccess : Success (getValue fuel uv) before.core
          (.unenumerated (some oldHandle) scs) readAfter := by
        rw [Success, reading]
        exact List.mem_singleton_self _
      obtain ⟨found, _lookup, stored, _readState⟩ :=
        (getValue_success fuel uv before.core readAfter (.unenumerated (some oldHandle) scs)).mp readSuccess
      obtain ⟨old, oldLookup, available, closed⟩ := realized found.representative oldHandle scs stored
      have same : old = oldValue := Option.some.inj (oldLookup.symm.trans decoded)
      subst old
      have resources := SourcePruningOuterNarrow.narrow_resources profile property holeKey fits admits metadata
        fuel uv oldValue caller.checked.native.machine.heap value heap narrowed initial.ready.semantic
        initial.ready.costs available closed
        (SourceCurrentConstrainedCapRequiredResources.of_checked bounded) known
      change Fits (headProfile profile) reached.checked ∧ Heap property reached.checked.native.machine.heap
      rw [reachedAt]
      exact ⟨⟨resources.1.nodes, resources.1.edges, bounded.domains, resources.1.stored⟩, resources.2⟩

end MicroCFTA.SourcePruningEnumerationSelectedStep

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSelectedStep (PrefixValid Resources runPrefix)
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

/-- A current packet derives prefix validity, resources and the packet at the actual returned caller. -/
theorem packet_prefix_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        selected caller before memos.query
      PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (bound + extra) selected caller before memos observed ∧
      Resources profile property caller observed ∧
      match observed with
      | .parked _ (some after) _ => Packet formulas solver inventory caller memos metadata after
      | .narrowed _ _ reached queries _ (some after) _ _ =>
          ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries ∧
            Packet formulas solver inventory reached final metadata after
      | _ => True := by
  obtain ⟨bound, complete⟩ := packet_prefix_complete holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  refine ⟨bound, ?_⟩
  intro extra selected chosen
  have valid := complete extra selected chosen
  exact ⟨valid,
    SourcePruningEnumerationSelectedStep.prefix_resources holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata formulas solver inventory (bound + extra) selected caller before memos profile property
      packet.context realized bounded known _ valid,
    prefix_packet holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (bound + extra) selected caller memos before packet _ valid⟩

end MicroCFTA.SourcePruningEnumerationRecursive
