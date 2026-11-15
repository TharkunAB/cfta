import MicroCFTA.SourceSynthesisCurrentNoStopSourceEntry
import MicroCFTA.SourceSynthesisCurrentInitialOuterNarrowFacts
import MicroCFTA.SourcePruningEnumerationInitialPacket
import MicroCFTA.SourcePruningEnumerationPrefixCompletion
import MicroCFTA.SourcePruningEnumerationIdentity

/-!
# The first real prefix from the original source initializer

The initializer derives the initial packet and the selected slot.
One finite bound runs the real narrowing prefix.
The result rejects Empty or retains the actual indexed cache and callback.
The proof-only finish expression does not run a legacy continuation.
-/
namespace MicroCFTA.SourceSynthesisCurrentFirstRealPrefix
open Cache EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSelectedStep (Result PrefixValid Valid finish runPrefix)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf 0 0 0 0 0 0 observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf 0 0 0 0 0 0 observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩

private theorem initial_narrowed_receipt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : EnumerationState.Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel handle : Nat) (rootValue : Node) (caller : Caller width) (before : Cached) (memos : Memos)
    (initialCore : before.core = EnumerationState.initial handle)
    (decoded : lookupNode caller.checked.native.machine.heap handle = some rootValue)
    (clear : MergedOrdinaryHeight.recursiveBoundary rootValue = false)
    (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges
      none (fun _ _ => none) metadata formulas solver inventory (fuel + 1) 0 caller before memos observed) :
    ∃ (checked : Core) (value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
      (selectedAction : EnumerateM Symbol Constraint Unit) (reached : Caller width) (final : Memos)
      (action : Option (List (Except EnumerationState.Error (Unit × Core))))
      (candidate : Option Cached)
      (right : Option (List (Except EnumerationState.Error ((Bool × Metadata Typing) × Core)))),
      observed = .narrowed checked (.done (value, some selectedAction) heap)
        reached memos.query action candidate right none ∧
      SourcePruningOuterNarrow.narrow holeKey fits admits metadata (fuel + 1) 0 rootValue
        caller.checked.native.machine.heap = .done value heap ∧
      Post formulas solver inventory caller reached final ∧ final.query = memos.query ∧
      ((value = .empty ∧ action = some [] ∧ candidate = none ∧ right = none) ∨
        ∃ (newHandle : Nat) (after : Cached), value ≠ .empty ∧ encodeNode value = some newHandle ∧
          action = some [.ok ((), after.core)] ∧ candidate = some after ∧
          SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after ∧ Safe after.core ∧
          EnumerationReferences.PendingReferences after.core ∧ EnumerationDriver.Ready 0 after.core ∧
          after.core.values[0]? = some (.unenumerated (some newHandle) []) ∧
          after.waiting = before.waiting ∧ right = some [.ok ((false, metadata), after.core)]) := by
  have readExact : ExceptT.run (getValue (fuel + 1) 0 before.core) =
      [.ok (.unenumerated (some handle) [], before.core)] := by
    rw [initialCore]
    rfl
  have checkExact : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap (fuel + 1) 0 handle [] before.core) =
      [.ok (false, before.core)] := by
    simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, clear,
      Bool.false_eq_true, ite_false]
    rfl
  have full := valid.2.1
  cases observed with
  | stopped _ _ =>
      obtain ⟨_, _, _, _, impossible⟩ := full
      exact False.elim impossible
  | parked _checked _candidate _raw =>
      obtain ⟨oldHandle, scs, readAfter, reading, checking, _rest⟩ := full
      have readSame := Except.ok.inj (List.cons.inj (reading.symm.trans readExact)).1
      have slotSame := Prod.mk.inj readSame
      have valueSame := UVarValue.unenumerated.inj slotSame.1
      have oldHandleSame := Option.some.inj valueSame.1
      have scsSame := valueSame.2
      have readAfterSame := slotSame.2
      rw [oldHandleSame, scsSame, readAfterSame, checkExact] at checking
      cases checking
  | narrowed checked prepared reached queries action candidate right ordinary =>
      have ordinaryNone : ordinary = none := valid.1
      subst ordinary
      obtain ⟨_finishedOrdinary, finished⟩ := finish_preserves checkEmpty InternedEdgeResidency.nodeEdges
        (.narrowed checked prepared reached queries action candidate right (none : Option _))
      rw [finished] at full
      obtain ⟨oldHandle, scs, readAfter, reading, _checking, oldValue, value, heap, selectedAction,
        final, oldDecoded, narrowed, _prepared, preparedEq, _reachedEq, queriesEq, post, finalQuery,
        shape⟩ := full
      have readSame := Except.ok.inj (List.cons.inj (reading.symm.trans readExact)).1
      have slotSame := Prod.mk.inj readSame
      have valueSame := UVarValue.unenumerated.inj slotSame.1
      have oldHandleSame := Option.some.inj valueSame.1
      have scsSame := valueSame.2
      have oldDecodedRoot : lookupNode caller.checked.native.machine.heap handle = some oldValue := by
        simpa only [oldHandleSame] using oldDecoded
      have oldValueSame : oldValue = rootValue := Option.some.inj (oldDecodedRoot.symm.trans decoded)
      rw [oldValueSame] at narrowed
      refine ⟨checked, value, heap, selectedAction, reached, final, action, candidate, right, ?_,
        narrowed, post, ?_, ?_⟩
      · rw [preparedEq, queriesEq]
      · exact finalQuery.trans queriesEq
      · rcases shape with empty | live
        · exact Or.inl ⟨empty.1, empty.2.1, empty.2.2.1, empty.2.2.2.1⟩
        · obtain ⟨newHandle, after, nonempty, encoded, actionEq, candidateEq, cacheValid, safe,
            pending, ready, stored, waiting, rightEq, _ordinaryEq, _ranges⟩ := live
          refine Or.inr ⟨newHandle, after, nonempty, encoded, actionEq, candidateEq,
            cacheValid, safe, pending, ready, ?_, waiting, rightEq⟩
          simpa only [scsSame] using stored

/-- Original source initialization derives a finite real prefix and its exact branch receipts. -/
theorem accepted_first_real_prefix
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : EnumerationState.Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    ∃ fields cache handle bound,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols whole)) Cache.emptyState fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) sourceHeap ∧
      Context formulas solver
        (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols whole) rootValue sourceHeap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap)
        SourceCurrentAllocatedPartialInitialization.globals ∧
      sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      encodeNode rootValue = some handle ∧ lookupNode sourceHeap handle = some rootValue ∧
      let caller := SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap
      let startup : Cached := ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩
      let inventory := SourceCurrentAllocatedPartialInitialization.inventory
        (ordinarySymbols whole) rootValue sourceHeap built
      let memos := SourceCurrentAllocatedPartialInitialization.globals
      runPrefix holeKey fits admits graph templates none (fun _ _ => none) metadata
        0 0 0 0 0 0 0 caller startup memos.query =
        .stopped [.error .representativeFuel] none ∧
      ∀ extra,
        let workFuel := bound + extra + 1
        let observed := runPrefix holeKey fits admits graph templates none (fun _ _ => none) metadata
          workFuel workFuel workFuel workFuel workFuel workFuel 0 caller startup memos.query
        PrefixValid holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges
          none (fun _ _ => none) metadata formulas solver inventory workFuel 0 caller startup memos observed ∧
        ∃ (checked : Core) (value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (selectedAction : EnumerateM Symbol Constraint Unit) (reached : Caller width) (final : Memos)
          (action : Option (List (Except EnumerationState.Error (Unit × Core))))
          (candidate : Option Cached)
          (right : Option (List (Except EnumerationState.Error ((Bool × Metadata Typing) × Core)))),
          observed = .narrowed checked (.done (value, some selectedAction) heap)
            reached memos.query action candidate right none ∧
          SourcePruningOuterNarrow.narrow holeKey fits admits metadata workFuel 0 rootValue sourceHeap =
            .done value heap ∧
          Post formulas solver inventory caller reached final ∧ final.query = memos.query ∧
          SourceEqualityRequiredCache.Ordinary value ∧
          (rootValue = .empty → value = .empty ∧ heap = sourceHeap) ∧
          ((value = .empty ∧ action = some [] ∧ candidate = none ∧ right = none) ∨
            ∃ (newHandle : Nat) (after : Cached), value ≠ .empty ∧ encodeNode value = some newHandle ∧
              action = some [.ok ((), after.core)] ∧ candidate = some after ∧
              SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after ∧ Safe after.core ∧
              EnumerationReferences.PendingReferences after.core ∧ EnumerationDriver.Ready 0 after.core ∧
              after.core.values[0]? = some (.unenumerated (some newHandle) []) ∧
              after.waiting = startup.waiting ∧ right = some [.ok ((false, metadata), after.core)]) := by
  obtain ⟨fields, cache, receipt, fieldFacts, context, _stored, clear, handle, encoded, decoded,
      decision, _entryEquation⟩ :=
    SourceSynthesisCurrentNoStopSourceEntry.accepted_no_stop_eager_entry (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      formulas solver holeKey fits admits graph templates checkEmpty 0 1 metadata
  have initialized := SourceCurrentAllocatedPartialInitialization.constructed width receipt.history
    Cache.empty_valid (ordinarySymbols whole) (fun _ member => member)
    rootValue sourceHeap built formulas solver
  obtain ⟨_identity, _emptySame, _emptyReady, available, closed, _original⟩ := initialized.2
  let caller := SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap
  let startup : Cached := ⟨EnumerationState.initial handle,
    fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
    fun _ => none⟩
  let inventory := SourceCurrentAllocatedPartialInitialization.inventory
    (ordinarySymbols whole) rootValue sourceHeap built
  let memos := SourceCurrentAllocatedPartialInitialization.globals
  obtain ⟨packetHandle, packetEncoded, _packetDecoded, packet, _canonical, _initialStored,
      _suspendedBound, _counts, _flags⟩ :=
    SourcePruningEnumerationRecursive.initial_packet formulas solver inventory caller memos metadata
      rootValue context available closed emptyPending
  have handleSame : packetHandle = handle := Option.some.inj (packetEncoded.symm.trans encoded)
  subst packetHandle
  obtain ⟨bound, completed⟩ := SourcePruningEnumerationSelectedStep.restart_prefix_complete
    holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
    metadata formulas solver inventory caller memos startup 0 context packet.safe packet.pending packet.valid decision
  refine ⟨fields, cache, handle, bound, receipt, fieldFacts, context, stored, encoded, decoded, ?_, ?_⟩
  · rfl
  · intro extra
    let workFuel := bound + extra + 1
    let observed := runPrefix holeKey fits admits graph templates none (fun _ _ => none) metadata
      workFuel workFuel workFuel workFuel workFuel workFuel 0 caller startup memos.query
    have prefixValid : PrefixValid holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges
        none (fun _ _ => none) metadata formulas solver inventory workFuel 0 caller startup memos observed := by
      exact completed (extra + 1)
    obtain ⟨checked, value, heap, selectedAction, reached, final, action, candidate, right,
        observedEq, narrowed, post, finalQuery, shape⟩ :=
      initial_narrowed_receipt holeKey fits admits graph templates checkEmpty metadata formulas solver inventory
        (bound + extra) handle rootValue caller startup memos rfl decoded clear observed prefixValid
    have narrowedSource : SourcePruningOuterNarrow.narrow holeKey fits admits metadata workFuel 0 rootValue
        sourceHeap = .done value heap := narrowed
    have resultOrdinary := (SourceSynthesisCurrentInitialOuterNarrowFacts.initial_outer_narrow_facts
      lib query signed whole accepted rootValue sourceHeap built metadata holeKey fits admits
      workFuel value heap narrowedSource).2.2
    have emptyCase : rootValue = .empty → value = .empty ∧ heap = sourceHeap := by
      intro rootEmpty
      have emptyRun : SourcePruningOuterNarrow.narrow holeKey fits admits metadata workFuel 0
          (.empty : Node) sourceHeap = .done .empty sourceHeap := by
        simp [SourcePruningOuterNarrow.narrow, SourcePruningEnumerationIdentity.narrowAt_empty]
      rw [rootEmpty, emptyRun] at narrowedSource
      have same := MergedSourceComparison.Result.done.inj narrowedSource
      exact ⟨same.1.symm, same.2.symm⟩
    exact ⟨prefixValid, checked, value, heap, selectedAction, reached, final, action, candidate, right,
      observedEq, narrowedSource, post, finalQuery, resultOrdinary, emptyCase, shape⟩

end MicroCFTA.SourceSynthesisCurrentFirstRealPrefix
