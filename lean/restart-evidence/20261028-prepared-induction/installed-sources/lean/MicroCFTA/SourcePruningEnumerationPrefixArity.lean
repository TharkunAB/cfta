import MicroCFTA.SourcePruningEnumerationNativeNarrowArity
import MicroCFTA.SourcePruningEnumerationPrefixResources

/-!
# Arity at the actual selected-prefix caller

The original prefix certificate identifies the actual narrowing equation.
Original realized storage supplies the value read by that equation.
The proof adds no new condition to the prefix completion producer.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem finish_retains_caller
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

/-- The original actual prefix certificate retains arity at its own caller endpoint. -/
theorem prefix_heap
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (heap : Heap caller.checked.native.machine.heap)
    (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .narrowed _ _ reached _ _ _ _ _ => Heap reached.checked.native.machine.heap
    | _ => Heap caller.checked.native.machine.heap := by
  have full := valid.2.1
  cases observed with
  | stopped _ _ | parked _ _ _ => exact heap
  | narrowed checked prepared reached queries action candidate right ordinary =>
      obtain ⟨_next, finished⟩ := finish_retains_caller checkEmpty edgesOf 0 0 0 0 0 uv
        (.narrowed checked prepared reached queries action candidate right ordinary)
      rw [finished] at full
      obtain ⟨oldHandle, scs, readAfter, reading, _checking, oldValue, value, nextHeap,
        _selectedAction, _final, decoded, narrowed, _prepared, _samePrepared, reachedAt,
        _queries, _post, _saved, _shape⟩ := full
      have readSuccess : Success (getValue fuel uv) before.core
          (.unenumerated (some oldHandle) scs) readAfter := by
        rw [Success, reading]
        exact List.mem_singleton_self _
      obtain ⟨found, _lookup, stored, _readState⟩ :=
        (getValue_success fuel uv before.core readAfter (.unenumerated (some oldHandle) scs)).mp readSuccess
      obtain ⟨old, oldLookup, available, _closed⟩ := realized found.representative oldHandle scs stored
      have same : old = oldValue := Option.some.inj (oldLookup.symm.trans decoded)
      subst old
      have retained := SourcePruningEnumerationNativeNarrowArity.outer_narrow_heap
        holeKey fits admits metadata fuel uv oldValue caller.checked.native.machine.heap
        initial.ready.good.heap.semantic.1.normal.facts heap available
      rw [narrowed] at retained
      change Heap reached.checked.native.machine.heap
      rw [reachedAt]
      exact retained

end MicroCFTA.SourcePruningEnumerationSelectedStep
