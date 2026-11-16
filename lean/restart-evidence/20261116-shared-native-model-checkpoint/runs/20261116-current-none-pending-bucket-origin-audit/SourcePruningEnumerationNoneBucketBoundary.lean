import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationDischargeBoundary
import MicroCFTA.EnumerationCanonicalWaiting

/-!
# Missing-domain buckets at an abstract done endpoint

The native candidate test ignores buckets when the node field is none.
The current Packet does not contain ProperState. A fabricated single-slot cache
therefore meets those local prerequisites while a descendant bucket remains.
This statement does not establish reachability from an accepted source.
-/
namespace MicroCFTA.SourcePruningEnumerationNoneBucketBoundary
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

set_option autoImplicit false
variable {Typing : Type} {width : Nat}

/-- A single valid proper descendant path names its own pending class. -/
def bucket : List Suspended := [⟨0, .branch [(0, .terminal)]⟩]

/-- One fabricated pending root has a missing domain and a nonempty bucket. -/
def core : EnumerationState.State Symbol Constraint :=
  ⟨1, UnionFind.withInitialValues [0], [.unenumerated none bucket], [], fun _ => [], []⟩

/-- All native candidate flags are false; the waiting map counts the stored self-reference. -/
def cache : EnumerationExpandableIndex.Cached Symbol Constraint :=
  ⟨core, fun _ => false, fun uv => if uv = 0 then some 1 else none⟩

private theorem only_value (value : UVarValue Symbol) (member : value ∈ core.values) :
    value = .unenumerated none bucket := by
  simpa [core] using member

private theorem safe_core : Safe core := by
  have storage : StorageValid core := by
    refine ⟨rfl, UnionFind.initial_total [0], ?_, ?_, ?_⟩
    · intro uv entry found
      have member : uv ∈ [0] := by
        by_cases present : uv ∈ [0]
        · exact present
        · simp only [core, UnionFind.withInitialValues, ite_eq_right present] at found
          cases found
      have rootEntry : UnionFind.Entry.root 1 = entry :=
        Option.some.inj (by
          simpa only [core, UnionFind.withInitialValues, ite_eq_left member] using found)
      subst entry
      have zero : uv = 0 := by simpa only [List.mem_singleton] using member
      subst uv
      exact ⟨by decide, trivial⟩
    · intro value member
      obtain rfl := only_value value member
      simp [core, SlotBound, bucket]
    · simp [core]
  refine ⟨storage, ?_⟩
  intro uv value found
  obtain rfl := only_value value (List.mem_of_getElem? found)
  refine ⟨fun _ => ⟨1, .root (UnionFind.read_initial [0] uv)⟩, ?_⟩
  intro _ impossible
  cases impossible

private theorem pending_core : EnumerationReferences.PendingReferences core := by
  intro uv fragment stored
  cases uv <;> simp [core] at stored

private theorem ordered_core : EnumerationOrder.Stratified core (fun _ => 0) 0 := by
  refine ⟨(fun _ _ _ => rfl), ?_, (fun _ _ _ _ => rfl)⟩
  intro uv fragment stored
  cases uv <;> simp [core] at stored

private theorem valid_cache (caller : SourceCurrentAllocatedPartialState.State width) :
    SourcePruningEnumerationNativeBranchCompletion.CacheValid caller cache := by
  refine ⟨id, ?_, safe_core.1, ?_, ?_, ?_⟩
  · intro uv
    exact ⟨1, .root (UnionFind.read_initial [0] uv)⟩
  · intro uv handle scs stored
    cases uv <;> simp [cache, core] at stored
  · intro uv
    by_cases zero : uv = 0
    · subst uv
      rfl
    · simp [cache, core, EnumerationCanonicalWaiting.canonicalValue,
        EnumerationWaitingIndex.total, EnumerationWaitingIndex.occurrences,
        references, bucket, zero, Ne.symm zero, EnumerationWaitingIndex.encode]
  · intro uv
    cases uv <;> rfl

theorem packet_done_can_retain_none_bucket
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (caller : SourceCurrentAllocatedPartialState.State width) (memos : EndpointMemoGateTrace.Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory caller memos)
    (emptyPending : metadata.pending = []) :
    SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata cache ∧
    SourcePruningEnumerationRestart.decision none order metadata cache = some .done ∧
    cache.core.values[0]? = some (.unenumerated none bucket) ∧
    bucket ≠ [] ∧ ¬EnumerationProgress.ProperState cache.core
 := by
  have packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata cache := by
    refine ⟨context, safe_core, pending_core, valid_cache caller, ⟨(fun _ => 0), 0, ordered_core⟩, ?_⟩
    intro group member
    rw [emptyPending] at member
    cases member
  have done : SourcePruningEnumerationRestart.decision none order metadata cache = some .done := by
    apply (SourcePruningEnumerationRestart.done_iff_candidates_nil order metadata cache).mpr
    simp [cache, EnumerationIndexSelection.candidates]
  have nonempty : bucket ≠ [] := by
    simp [bucket]
  refine ⟨packet, done, rfl, nonempty, ?_⟩
  intro proper
  have empty : bucket = [] := proper (.unenumerated none bucket) (by simp [cache, core])
  exact nonempty empty

end MicroCFTA.SourcePruningEnumerationNoneBucketBoundary
