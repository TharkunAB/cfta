import MicroCFTA.SourcePruningEnumerationFiniteSiblingCoverage
import MicroCFTA.SourcePruningEnumerationSelectorLanguage
import MicroCFTA.SourcePruningEnumerationFiniteResources

/-!
# A parent model reaches a finite recursive invocation or an earlier hook stop

The original stored model supplies an accepting selected edge.
A permutation selector retains that edge at an actual index.
The complete primary packet and uniform observer remain available.
The chosen invocation can stop after its captured edge completes.
An earlier hook stop retains its outputs, reason and optional endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
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

/-- An original parent model reaches its accepting invocation or an exact earlier recursive stop. -/
theorem parent_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selectedRows : selectedEdges.Perm storedEdges)
    (supported : ∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment before.core) :
    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      ((∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata before ∧
      Fits (stage recursiveFuel seed capturedMass inherited selectedEdges.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited selectedEdges.length).1)
        afterCaller.checked.native.machine.heap ∧
      processed.length ≤ selectedEdges.length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < selectedEdges.length ∧
        OutputAt recursiveFuel formulas solver caller seed capturedMass inherited index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      ∀ extra,
        let work := bound + extra
        let hook := continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order work recursiveFuel)
          graph templates stop order work metadata uv
        ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint), selectedEdges[index]? = some chosen →
          (∀ earlier ∈ selectedEdges.take index, arityAllows earlier.children.length scs = true →
            SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none) →
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core →
            InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient chosen (assignment uv) →
            ∃ (eventIndex : Nat) (eventEdge : EdgeValue Symbol Constraint)
              (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
              (prefixReceipts : List (Receipt (bits + 2))) (prefixOutputs : List (Output (bits + 2) Typing))
              (fragment : Fragment) (branchCaller : Caller (bits + 2)) (branchQueries : Queries)
              (afterCache : Cached) (branchInventory : Inventory) (branchMemos : Memos),
              eventIndex ≤ index ∧ selectedEdges[eventIndex]? = some eventEdge ∧
              prefixReceipts.length = eventIndex ∧
              Post formulas solver headInventory caller headCaller headMemos ∧
              Packet formulas solver headInventory headCaller headMemos metadata before ∧
              Fits (stage recursiveFuel seed capturedMass inherited eventIndex).2 headCaller.checked ∧
              Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited eventIndex).1)
                headCaller.checked.native.machine.heap ∧
              SourcePruningEnumerationFiniteReservation.HeadReserved bits recursiveFuel
                (stage recursiveFuel seed capturedMass inherited eventIndex) capturedMass inherited ∧
              SourcePruningEnumerationNativeContinuations.run hook checkEmpty work work work work work
                uv scs before (selectedEdges.take eventIndex) caller memos.query =
                .complete prefixReceipts prefixOutputs headCaller headMemos.query ∧
              Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
              branchMemos.query = branchQueries ∧
              SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work uv scs
                eventEdge headCaller before headMemos.query =
                some (.complete fragment branchCaller branchQueries afterCache) ∧
              SourcePruningEnumerationHookInvocation.Invocation hook checkEmpty work work work work work
                uv scs before selectedEdges caller memos.query fragment branchCaller branchQueries afterCache ∧
              ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited eventIndex
                (.complete fragment branchCaller branchQueries afterCache) ∧
              ((eventIndex = index ∧ eventEdge = chosen ∧
                  ∃ extended : Nat → Language.Term Symbol,
                    (∀ old < before.core.counter, extended old = assignment old) ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient caller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended before.core ∧
                    Fragments.fill extended fragment = assignment uv ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient branchCaller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended afterCache.core) ∨
                (eventIndex < index ∧
                  ∃ (hookOutputs : List (Output (bits + 2) Typing)) (reason : Failure (bits + 2) Typing)
                    (reached : Option (Caller (bits + 2) × Queries)),
                    hook fragment branchCaller branchQueries afterCache = .stopped hookOutputs reason reached ∧
                    result = .stopped prefixReceipts (prefixOutputs ++ hookOutputs)
                      (.continuation (.complete fragment branchCaller branchQueries afterCache) reason reached) ∧
                    SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
                      (stage recursiveFuel seed capturedMass inherited (eventIndex + 1))
                      (.stopped hookOutputs reason reached)))) ∧
      ∃ (index : Nat) (chosen : EdgeValue Symbol Constraint),
        selectedEdges[index]? = some chosen ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient chosen (assignment uv) ∧
      ∀ extra,
        let work := bound + extra
        let hook := continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order work recursiveFuel)
          graph templates stop order work metadata uv
            ∃ (eventIndex : Nat) (eventEdge : EdgeValue Symbol Constraint)
              (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
              (prefixReceipts : List (Receipt (bits + 2))) (prefixOutputs : List (Output (bits + 2) Typing))
              (fragment : Fragment) (branchCaller : Caller (bits + 2)) (branchQueries : Queries)
              (afterCache : Cached) (branchInventory : Inventory) (branchMemos : Memos),
              eventIndex ≤ index ∧ selectedEdges[eventIndex]? = some eventEdge ∧
              prefixReceipts.length = eventIndex ∧
              Post formulas solver headInventory caller headCaller headMemos ∧
              Packet formulas solver headInventory headCaller headMemos metadata before ∧
              Fits (stage recursiveFuel seed capturedMass inherited eventIndex).2 headCaller.checked ∧
              Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited eventIndex).1)
                headCaller.checked.native.machine.heap ∧
              SourcePruningEnumerationFiniteReservation.HeadReserved bits recursiveFuel
                (stage recursiveFuel seed capturedMass inherited eventIndex) capturedMass inherited ∧
              SourcePruningEnumerationNativeContinuations.run hook checkEmpty work work work work work
                uv scs before (selectedEdges.take eventIndex) caller memos.query =
                .complete prefixReceipts prefixOutputs headCaller headMemos.query ∧
              Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
              branchMemos.query = branchQueries ∧
              SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work uv scs
                eventEdge headCaller before headMemos.query =
                some (.complete fragment branchCaller branchQueries afterCache) ∧
              SourcePruningEnumerationHookInvocation.Invocation hook checkEmpty work work work work work
                uv scs before selectedEdges caller memos.query fragment branchCaller branchQueries afterCache ∧
              ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited eventIndex
                (.complete fragment branchCaller branchQueries afterCache) ∧
              ((eventIndex = index ∧ eventEdge = chosen ∧
                  ∃ extended : Nat → Language.Term Symbol,
                    (∀ old < before.core.counter, extended old = assignment old) ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient caller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended before.core ∧
                    Fragments.fill extended fragment = assignment uv ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient branchCaller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended afterCache.core) ∨
                (eventIndex < index ∧
                  ∃ (hookOutputs : List (Output (bits + 2) Typing)) (reason : Failure (bits + 2) Typing)
                    (reached : Option (Caller (bits + 2) × Queries)),
                    hook fragment branchCaller branchQueries afterCache = .stopped hookOutputs reason reached ∧
                    result = .stopped prefixReceipts (prefixOutputs ++ hookOutputs)
                      (.continuation (.complete fragment branchCaller branchQueries afterCache) reason reached) ∧
                    SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
                      (stage recursiveFuel seed capturedMass inherited (eventIndex + 1))
                      (.stopped hookOutputs reason reached))) := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry storedEdges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have model := satisfied.1.2 uv
  simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
    List.forall_mem_map] at model
  have parentAccepted : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient
      (.node parentEntry storedEdges depth free) (assignment uv) :=
    (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp model.1
  obtain ⟨chosen, offered, _member, _resident, accepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap packet.context.ready.semantic.ready parentEntry storedEdges
      selectedEdges depth free available selectedRows (SourceEqualityPCSGuard.holds formulas solver)
      ambient (assignment uv) parentAccepted
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp offered
  have recursive : SourcePruningEnumerationRecursive.Complete (bits := bits)
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel :=
    SourcePruningEnumerationRecursive.finite_complete
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result,
    running, post, captured, returnedFits, returnedKnown, length, receipts, outputResources, shape, accepting⟩ :=
    alternatives_finite_complete_resources_accepting
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges
      selectedEdges depth free packet ready stored decoded (fun edge member => selectedRows.mem_iff.mp member)
      incoming bounded known selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved
  have prefixSupported : ∀ earlier ∈ selectedEdges.take index,
      arityAllows earlier.children.length scs = true →
      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
    intro earlier member allowed
    exact supported earlier (List.mem_of_mem_take member) allowed
  refine ⟨bound, processed, outputs, afterCaller, next, final, result,
    ⟨running, post, captured, returnedFits, returnedKnown, length, receipts, outputResources, shape, accepting⟩,
    index, chosen, found, accepted, ?_⟩
  intro extra
  exact accepting extra index chosen found prefixSupported ambient assignment satisfied accepted

end MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources
