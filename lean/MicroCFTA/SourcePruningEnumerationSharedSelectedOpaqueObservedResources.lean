import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueResources
import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueStability
import MicroCFTA.SourcePruningEnumerationSharedChildResources
import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedHookCertificates
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds

/-!
# Resources for an observed completed actual shared opaque receipt

The current completed receipt supplies every original resource conclusion.
Larger-bound replay identifies it with the result derived from the same inputs.
No future observation or callback resource is an input premise.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "receiptAdvance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual completed receipt has all resources derived from the original inputs. -/
theorem observed_complete_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (target handle : Nat) (scs : List Suspended)
    (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (r n p h k : Nat) (fragment : Fragments.Fragment Symbol)
    (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (observed : run checkEmpty r n p h k target scs value caller before memos.query =
      some (.complete fragment reached saved after)) :
    ∃ (bound : Nat) (final : Memos) (next : Inventory),
      (∀ extra, run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        target scs value caller before memos.query = some (.complete fragment reached saved after)) ∧
      Post formulas solver next caller reached final ∧ final.query = saved ∧
      receiptAdvance (.complete fragment reached saved after) = some (reached, saved) ∧
      Admitted target (.complete fragment reached saved after) ∧ Pending (.complete fragment reached saved after) ∧ FragmentHistory before.core (.complete fragment reached saved after) ∧
      Fits (advance seed (scs.length + 1)).2 reached.checked ∧
      Heap (fun guard => guard ∈ (advance seed (scs.length + 1)).1) reached.checked.native.machine.heap ∧
      ((∃ produced finished, (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete fragment reached saved after) = .complete produced reached saved finished ∧
          Packet formulas solver next reached final metadata finished ∧
          finished.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound finished.core ≤ suspendedBound before.core + scs.length) ∨
        (∃ finished outer waiting, (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete fragment reached saved after) = .stopped []
          (.ok (some []), reached, saved, outer, waiting) (some finished) ∧
          finished.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound finished.core ≤ suspendedBound before.core + scs.length) ∨
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete fragment reached saved after) = .rejected caller memos.query before) ∧
      FinalizationAt checkEmpty bound target scs value caller before memos.query (.complete fragment reached saved after) := by
  obtain ⟨bound, canonicalReceipt, canonicalReached, canonicalSaved, final, next, retained⟩ :=
    opaque_complete_resources seed formulas solver inventory caller memos metadata before
      checkEmpty target handle scs value packet ready stored incoming available closed dispatch
      bounded reserved known
  let common : Nat := bound + r + n + p + h + k
  have observedLater := complete_stable
    (R := common) (N := common) (P := common) (H := common) (K := common)
    observed (by dsimp [common]; omega) (by dsimp [common]; omega)
      (by dsimp [common]; omega) (by dsimp [common]; omega) (by dsimp [common]; omega)
  have canonicalLater := retained.1 (r + n + p + h + k)
  have sameFuel : bound + (r + n + p + h + k) = common := by dsimp [common]; omega
  rw [sameFuel] at canonicalLater
  have sameReceipt : canonicalReceipt = .complete fragment reached saved after :=
    Option.some.inj (canonicalLater.symm.trans observedLater)
  subst canonicalReceipt
  have endpoint : (reached, saved) = (canonicalReached, canonicalSaved) :=
    Option.some.inj retained.2.2.2.1
  obtain ⟨sameCaller, sameQueries⟩ := Prod.mk.inj endpoint
  subst canonicalReached canonicalSaved
  exact ⟨bound, final, next, retained⟩

end MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
