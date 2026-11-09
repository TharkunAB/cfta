import MicroCFTA.SourcePruningEnumerationPrefixResources
import MicroCFTA.SourcePruningEnumerationPrefixCheckpoint
import MicroCFTA.SourcePruningEnumerationSharedHookCertificates

/-!
# Current facts at the selected shared prefix

The actual selected prefix uses the unchanged heap-only narrowing call.
Its current facts contain no ordinary continuation or finish execution.
The Right callback retains the original metadata. The parked restart also
returns its original metadata whenever it returns a singleton.

Larger bounds retain the branch endpoints. A prepared action can capture
its representative fuel, so the checkpoint permits a different action.
The resource profile is headProfile. This prefix runs no extra prepared
Mu or union normalization.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open InternedProbeProvenance SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSelectedStep (runPrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Observed" => SourcePruningEnumerationSelectedStep.Result
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Keep the actual parked, Empty or nonempty prefix packet. -/
def CurrentPrefixFacts
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos) : Observed width Typing → Prop
  | .stopped _ _ => False
  | .parked checked candidate raw =>
      ∃ after : Cached, candidate = some after ∧ after.core = checked ∧
        raw = some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata after checked)) ∧
        Packet formulas solver inventory caller memos metadata after
  | .narrowed _checked prepared reached queries action candidate right ordinary =>
      ordinary = none ∧ queries = memos.query ∧
      ∃ (value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
        (selectedAction : EnumerateM Symbol Constraint Unit) (final : Memos),
        prepared = .done (value, some selectedAction) heap ∧
        reached = SourceCurrentAllocatedPartialState.advance caller
          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge ∧
        Post formulas solver inventory caller reached final ∧ final.query = queries ∧
        ((value = .empty ∧ action = some [] ∧ candidate = none ∧ right = none) ∨
          ∃ (newHandle : Nat) (scs : List Suspended) (after : Cached),
            value ≠ .empty ∧ encodeNode value = some newHandle ∧
            action = some [.ok ((), after.core)] ∧ candidate = some after ∧
            right = some [.ok ((false, metadata), after.core)] ∧
            EnumerationDriver.Ready uv after.core ∧
            after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
            after.waiting = before.waiting ∧ Packet formulas solver inventory reached final metadata after)

/-- Current prefix facts retain the exact reached native resource bounds. -/
def CurrentPrefixResources
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (profile : Profile) (property : Constraint → Prop) (observed : Observed width Typing) : Prop :=
  CurrentPrefixFacts stop order metadata formulas solver inventory uv caller before memos observed ∧
    SourcePruningEnumerationSelectedStep.Resources profile property caller observed

private theorem finish_fields
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (uv : Nat) (observed : Observed width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ =>
        SourcePruningEnumerationSelectedStep.finish checkEmpty edgesOf 0 0 0 0 0 uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, SourcePruningEnumerationSelectedStep.finish checkEmpty edgesOf 0 0 0 0 0 uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold SourcePruningEnumerationSelectedStep.finish
      split <;> simp_all only [SourcePruningEnumerationSelectedStep.Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩

private theorem current_of_valid
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (observed : Observed width Typing)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed) :
    CurrentPrefixFacts stop order metadata formulas solver inventory uv caller before memos observed := by
  have full := valid.2.1
  have cached := SourcePruningEnumerationPrefixPacket.prefix_cache_valid holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed valid
  cases observed with
  | stopped _ _ =>
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, impossible⟩ := full
      exact impossible
  | parked checked candidate raw =>
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, after, candidateSame, coreSame,
        _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
      subst candidate
      have pureFacts : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧
          Safe after.core ∧ EnumerationReferences.PendingReferences after.core ∧
          after.core.counter = before.core.counter ∧
          ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            EnumerationOrder.Stratified after.core level frontier := by
        exact cached
      obtain ⟨cacheValid, safe, pending, counter, ordered⟩ := pureFacts
      refine ⟨after, rfl, coreSame, rawSame, packet.context, safe, pending, cacheValid, ?_, ?_⟩
      · obtain ⟨level, frontier, originalOrder⟩ := packet.ordered
        exact ⟨level, frontier, ordered level frontier originalOrder⟩
      · simpa only [counter] using packet.bounded
  | narrowed checked prepared reached queries action candidate right ordinary =>
      obtain ⟨next, finished⟩ := finish_fields checkEmpty edgesOf uv
        (.narrowed checked prepared reached queries action candidate right ordinary)
      rw [finished] at full
      obtain ⟨_oldHandle, scs, _readAfter, _reading, _checking, _oldValue, value, heap,
        selectedAction, final, _decoded, _narrowed, _prepared, preparedSame, reachedSame,
        querySame, post, saved, shape⟩ := full
      refine ⟨valid.1, querySame, value, heap, selectedAction, final, preparedSame, reachedSame, post, saved, ?_⟩
      rcases shape with ⟨empty, actionSame, noCache, noRight, _oldOrdinary⟩ |
        ⟨newHandle, after, nonempty, encoded, actionSame, candidateSame, _cacheValid, _safe,
          _pending, ready, stored, waiting, rightSame, _oldOrdinary, _continuation⟩
      · exact .inl ⟨empty, actionSame, noCache, noRight⟩
      · subst candidate
        have pureFacts : SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after ∧
            Safe after.core ∧ EnumerationReferences.PendingReferences after.core ∧
            after.core.counter = before.core.counter ∧
            ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
              EnumerationOrder.Stratified after.core level frontier := by
          exact cached
        obtain ⟨cacheValid, safe, pending, counter, ordered⟩ := pureFacts
        refine .inr ⟨newHandle, scs, after, nonempty, encoded, actionSame, rfl, rightSame,
          ready, stored, waiting, post.context, safe, pending, cacheValid, ?_, ?_⟩
        · obtain ⟨level, frontier, originalOrder⟩ := packet.ordered
          exact ⟨level, frontier, ordered level frontier originalOrder⟩
        · simpa only [counter] using packet.bounded

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- Current input data derive the actual prefix packet at every sufficient common bound. -/
theorem prefix_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          selected caller before memos.query) := by
  classical
  obtain ⟨bound, complete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet profile property bounded known
  refine ⟨bound, ?_⟩
  intro extra selected chosen
  obtain ⟨valid, resources, _oldPacket⟩ := complete extra selected chosen
  exact ⟨current_of_valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory (bound + extra) selected caller before memos packet _ valid, resources⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- One selected prefix retains its branch endpoints at all sufficient bounds.
The nonempty branch permits a distinct prepared action at each bound. -/
theorem checkpoint_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (uv : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ fuel,
      (∃ checked : Cached, ∀ extra,
        runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .parked checked.core (some checked)
            (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core))) ∧
        CurrentPrefixResources stop order metadata formulas solver inventory uv caller before memos profile property
            (runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query)) ∨
      (∃ (checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint), ∀ extra,
        runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
            memos.query (some []) none none none ∧
        CurrentPrefixResources stop order metadata formulas solver inventory uv caller before memos profile property
            (runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query)) ∨
      (∃ (checked : Core) (value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (after : Cached), value ≠ .empty ∧ ∀ extra, ∃ action : EnumerateM Symbol Constraint Unit,
        runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .narrowed checked (.done (value, some action) heap)
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
            memos.query (some [.ok ((), after.core)]) (some after)
            (some [.ok ((false, metadata), after.core)]) none ∧
        CurrentPrefixResources stop order metadata formulas solver inventory uv caller before memos profile property
            (runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query)) := by
  classical
  have picked : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨fuel, branches⟩ := SourcePruningEnumerationSelectedStep.prefix_checkpoint_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before (order metadata) uv roots packet.context packet.safe packet.pending picked
    realized paths counts flags
  have current (extra : Nat)
      (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
        checkEmpty edgesOf stop order metadata formulas solver inventory (fuel + extra) uv caller before memos
        (runPrefix holeKey fits admits graph templates stop order metadata
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          uv caller before memos.query)) :
      CurrentPrefixResources stop order metadata formulas solver inventory uv caller before memos profile property
        (runPrefix holeKey fits admits graph templates stop order metadata
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          uv caller before memos.query) := by
    exact ⟨current_of_valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory (fuel + extra) uv caller before memos packet _ valid,
      SourcePruningEnumerationSelectedStep.prefix_resources holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (fuel + extra) uv caller before memos profile property
        packet.context realized bounded known _ valid⟩
  rcases branches with ⟨checked, stable⟩ | ⟨checked, heap, stable⟩ |
    ⟨checked, value, heap, after, nonempty, stable⟩
  · refine ⟨fuel, .inl ⟨checked, ?_⟩⟩
    intro extra
    obtain ⟨actual, valid⟩ := stable extra
    exact ⟨actual, current extra valid⟩
  · refine ⟨fuel, .inr (.inl ⟨checked, heap, ?_⟩)⟩
    intro extra
    obtain ⟨actual, valid⟩ := stable extra
    exact ⟨actual, current extra valid⟩
  · refine ⟨fuel, .inr (.inr ⟨checked, value, heap, after, nonempty, ?_⟩)⟩
    intro extra
    obtain ⟨action, actual, valid⟩ := stable extra
    exact ⟨action, actual, current extra valid⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- The actual successful Right callback carries the packet at its returned metadata. -/
theorem CurrentPrefixFacts.right_packet
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {metadata updated : Metadata Typing}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {uv : Nat} {caller : Caller width} {before after : Cached} {memos : Memos}
    {checked prepared reached queries action ordinary}
    (facts : CurrentPrefixFacts stop order metadata formulas solver inventory uv caller before memos
      (.narrowed checked prepared reached queries action (some after)
        (some [.ok ((false, updated), after.core)]) ordinary)) :
    updated = metadata ∧ ∃ final, Post formulas solver inventory caller reached final ∧
      final.query = queries ∧ Packet formulas solver inventory reached final updated after := by
  obtain ⟨_ordinary, _queries, _value, _heap, _selectedAction, final,
    _prepared, _reached, post, saved, shape⟩ := facts
  rcases shape with ⟨_empty, _action, impossible, _right⟩ |
    ⟨_newHandle, _scs, cached, _nonempty, _encoded, _action, sameCache, sameRight,
      _ready, _stored, _waiting, packet⟩
  · cases impossible
  · have equal : after = cached := Option.some.inj sameCache
    subst cached
    have sameMetadata : updated = metadata := by
      simpa only [Option.some.injEq, List.cons.injEq, Except.ok.injEq, Prod.mk.injEq,
        and_true, true_and] using sameRight
    refine ⟨sameMetadata, final, post, saved, ?_⟩
    simpa only [sameMetadata] using packet

end MicroCFTA.SourcePruningEnumerationSharedRecursive
