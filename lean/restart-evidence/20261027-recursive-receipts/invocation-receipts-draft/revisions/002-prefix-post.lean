import MicroCFTA.SourcePruningEnumerationHeadAdmission
import MicroCFTA.SourcePruningEnumerationHookInvocation

/-!
# Full head receipts on actual recursive sibling paths

The original resource schedule supplies each native head and callback.
Each suffix starts at the actual post-hook caller and full memo state.
Every observed hook input retains its own stable completed head receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint)
attribute [local irreducible] SourcePruningEnumerationFiniteReservation.step
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationFiniteReservation.step
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original admission supplies full receipts for every actual invoked recursive hook. -/
theorem alternatives_finite_invocation_receipts
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourcePruningEnumerationRecursive.Complete (bits := bits) holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length) :
    ∃ bound : Nat, ∀ extra (fragment : Fragment) (reached : Caller (bits + 2))
      (saved : Queries) (after : Cached),
      SourcePruningEnumerationHookInvocation.Invocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query fragment reached saved after →
      ∃ edge ∈ selectedEdges, ∃ (headSeed : Seed) (headInventory : Inventory)
        (headCaller : Caller (bits + 2)) (headMemos : Memos) (headBound : Nat)
        (returnedInventory : Inventory) (returnedMemos : Memos),
        Post formulas solver headInventory caller headCaller headMemos ∧
        SourcePruningEnumerationCapturedEdge.run checkEmpty
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          uv scs edge headCaller before headMemos.query = some (.complete fragment reached saved after) ∧
        SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
          headInventory headCaller headMemos metadata before checkEmpty uv scs edge headBound
          fragment reached saved after returnedInventory returnedMemos := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, ?_⟩
      intro extra fragment reached saved after invocation
      cases invocation
  | cons edge rest ih =>
      obtain ⟨headBound, receipt, middleCaller, headSaved, middleMemos, middleInventory,
        headRun, _headPost, _headQueries, _admitted, _pending, _history, _cacheBounds,
        _headFits, _headKnown, shape, completedReceipt⟩ :=
        SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_with_receipt
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
          seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges
          depth free edge packet ready stored decoded (selected edge List.mem_cons_self) incoming
          bounded known selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved.head
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, _resources, captured⟩
      · obtain ⟨unhandled, _allowed, _projected⟩ := unsupported
        subst receipt
        refine ⟨headBound, ?_⟩
        intro extra fragment reached saved after invocation
        have first := headRun extra
        cases invocation with
        | here observed =>
            rw [first] at observed
            cases observed
        | completed observed _continued _tail =>
            rw [first] at observed
            cases observed
        | other observed _notComplete actualAdvance _tail =>
            rw [first] at observed
            cases observed
            cases actualAdvance
      · cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨hookInventory, hookMemos, hookPost, hookQuery, hookCaptured, hookFits, hookKnown⟩ := captured
            obtain ⟨tailBound, tailReceipts⟩ :=
              ih (afterHook recursiveFuel seed capturedMass inherited) hookInventory hookCaller hookMemos hookCaptured
                (lookupNode_keeps _ _ hookPost.effects.keeps handle _ decoded)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) hookFits hookKnown reserved.tail
            let bound := headBound + tailBound
            refine ⟨bound, ?_⟩
            intro extra fragment reached saved after invocation
            let w := bound + extra
            have hl : headBound ≤ w := by dsimp [w, bound]; omega
            have tl : tailBound ≤ w := by dsimp [w, bound]; omega
            have first := headRun (w - headBound)
            rw [Nat.add_sub_of_le hl] at first
            have hooked := callbackRun (w - headBound)
            rw [Nat.add_sub_of_le hl] at hooked
            have tailAt := tailReceipts (w - tailBound) fragment reached saved after
            rw [Nat.add_sub_of_le tl, hookQuery] at tailAt
            cases invocation with
            | here observed =>
                have same : receipt = .complete fragment reached saved after :=
                  Option.some.inj (first.symm.trans observed)
                exact ⟨edge, List.mem_cons_self, seed, inventory, caller, memos, headBound,
                  middleInventory, middleMemos, Post.refl packet.context, observed,
                  completedReceipt fragment reached saved after same⟩
            | completed observed continued tail =>
                have same := Option.some.inj (first.symm.trans observed)
                rw [same] at hooked
                obtain ⟨_outputs, rfl, rfl⟩ :=
                  SourcePruningEnumerationNativeContinuations.HookResult.complete.inj (hooked.symm.trans continued)
                obtain ⟨chosen, member, headSeed, headInventory, headCaller, headMemos, localBound,
                  returnedInventory, returnedMemos, prefixPost, observedHead, certificate⟩ := tailAt tail
                exact ⟨chosen, List.mem_cons_of_mem _ member, headSeed, headInventory, headCaller, headMemos,
                  localBound, returnedInventory, returnedMemos, hookPost.trans prefixPost, observedHead, certificate⟩
            | other observed notComplete actualAdvance tail =>
                have same := Option.some.inj (first.symm.trans observed)
                have noncomplete : (match receipt with | .complete .. => False | _ => True) := by
                  rw [same]
                  exact notComplete
                have canonicalAdvance : advance receipt = some (hookCaller, hookQueries) := by
                  cases receipt with
                  | complete _ _ _ _ => cases noncomplete
                  | unhandled => cases advanced
                  | rejected actual queries cache | stopped fragments observation candidate =>
                      obtain ⟨_outputs, actualSame, queriesSame⟩ :=
                        SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                      rw [← actualSame, ← queriesSame]
                      exact advanced
                rw [← same] at actualAdvance
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (canonicalAdvance.symm.trans actualAdvance))
                obtain ⟨chosen, member, headSeed, headInventory, headCaller, headMemos, localBound,
                  returnedInventory, returnedMemos, prefixPost, observedHead, certificate⟩ := tailAt tail
                exact ⟨chosen, List.mem_cons_of_mem _ member, headSeed, headInventory, headCaller, headMemos,
                  localBound, returnedInventory, returnedMemos, hookPost.trans prefixPost, observedHead, certificate⟩
        | stopped headOutputs reason endpoint =>
            have completed : ∃ fragment actual queries cache, receipt = .complete fragment actual queries cache := by
              cases receipt with
              | complete fragment actual queries cache => exact ⟨fragment, actual, queries, cache, rfl⟩
              | unhandled => cases advanced
              | rejected actual queries cache | stopped fragments observation candidate =>
                  have impossible := callbackRun 0
                  cases impossible
            obtain ⟨firstFragment, firstCaller, firstQueries, firstCache, same⟩ := completed
            subst receipt
            refine ⟨headBound, ?_⟩
            intro extra fragment reached saved after invocation
            have first := headRun extra
            have hooked := callbackRun extra
            cases invocation with
            | here observed =>
                have same := Option.some.inj (first.symm.trans observed)
                exact ⟨edge, List.mem_cons_self, seed, inventory, caller, memos, headBound,
                  middleInventory, middleMemos, Post.refl packet.context, observed,
                  completedReceipt fragment reached saved after same⟩
            | completed observed continued _tail =>
                have same := Option.some.inj (first.symm.trans observed)
                rw [same] at hooked
                rw [hooked] at continued
                cases continued
            | other observed notComplete _actualAdvance _tail =>
                have same := Option.some.inj (first.symm.trans observed)
                rw [← same] at notComplete
                cases notComplete

end MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources
