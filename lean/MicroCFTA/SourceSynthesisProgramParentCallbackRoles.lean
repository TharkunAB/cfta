import MicroCFTA.SourceSynthesisProgramFragmentWrite
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourcePruningEnumerationSharedPreparedCallbackResources
import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.EnumerationFragmentHistory
import MicroCFTA.EnumerationPendingReplacement

/-!
# Program roles through actual parent finalization and recording

The current completed-child packet supplies all execution invariants.
Complete source rows and current child receipts supply the assembled layout.
One finalizer supplies its complete actual cache. One callback supplies its
complete stable metadata return. Neither recursive completion nor rank follows
from the fragment-role predicate alone.
-/
namespace MicroCFTA.SourceSynthesisProgramParentCallbackRoles
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open EnumerationDependencies EnumerationCompressionFrame InternedConstructorTemplates
open SourceSynthesisHereditaryProgramFields (EdgeFields)
open SourceSynthesisProgramEnumerationRoles (FragmentRoles ProgramSlots)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing : Type} {width : Nat}
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (SourcePruningEnumerationSharedPreparedRecursive.Output width Typing)
  (SourcePruningEnumerationSharedPreparedRecursive.Failure width Typing) width

private theorem cons_of_length (values : List Fragment) (count : Nat)
    (length : values.length = count + 1) :
    ∃ first rest, values = first :: rest ∧ rest.length = count := by
  cases values with
  | nil => simp only [List.length_nil] at length; omega
  | cons first rest => exact ⟨first, rest, rfl, by simp only [List.length_cons] at length; omega⟩

private theorem assembled_roles (valid : Constraint → Prop) (marked : Nat → Prop)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (fragments : List Fragment) (length : fragments.length = edge.children.length)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child) :
    FragmentRoles literal marked (.node edge.entry.key.symbol fragments) := by
  cases fields with
  | annotated edge _annotation _guard children _typed =>
      have one : fragments.length = 1 := by simpa only [children, List.length_cons, List.length_nil] using length
      obtain ⟨annotation, rfl⟩ := List.length_eq_one_iff.mp one
      exact .component edge.entry.key.symbol annotation
  | application edge _types _marker _function _argument symbol _guard children _typesTyped _markerTyped
      _functionFields _argumentFields =>
      have four : fragments.length = 4 := by simpa only [children, List.length_cons, List.length_nil] using length
      obtain ⟨annotation, rest, rfl, three⟩ := cons_of_length fragments 3 four
      obtain ⟨marker, rest, rfl, two⟩ := cons_of_length rest 2 three
      obtain ⟨function, rest, rfl, one⟩ := cons_of_length rest 1 two
      obtain ⟨argument, rest, rfl, zero⟩ := cons_of_length rest 0 one
      have empty : rest = [] := List.length_eq_zero_iff.mp zero
      subst rest
      rw [symbol]
      exact .application annotation marker function argument
        (childrenRoles 2 function (Or.inl ⟨symbol, Or.inl rfl⟩) rfl)
        (childrenRoles 3 argument (Or.inl ⟨symbol, Or.inr rfl⟩) rfl)
  | filter edge _goal _candidates symbol _guard children _goalTyped _candidateFields =>
      have two : fragments.length = 2 := by simpa only [children, List.length_cons, List.length_nil] using length
      obtain ⟨goal, rest, rfl, one⟩ := cons_of_length fragments 1 two
      obtain ⟨candidates, rest, rfl, zero⟩ := cons_of_length rest 0 one
      have empty : rest = [] := List.length_eq_zero_iff.mp zero
      subst rest
      rw [symbol]
      exact .filter goal candidates (childrenRoles 1 candidates (Or.inr ⟨symbol, rfl⟩) rfl)

private theorem slots_frame (valid : Constraint → Prop) (marked : Nat → Prop)
    (heap : NativeHeap) (before after : Core) (framed : Frame before after)
    (slots : ProgramSlots valid literal heap before marked) : ProgramSlots valid literal heap after marked := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv known
    simpa only [framed.counter] using slots.bounded uv known
  · intro uv known
    obtain ⟨size, path⟩ := slots.roots uv known
    exact ⟨size, (framed.reaches uv uv size).mpr path⟩
  · intro uv known
    exact EnumerationPendingReplacement.frame_incoming uv before after framed (slots.incoming uv known)
  · intro uv known
    obtain ⟨payload, stored, role⟩ := slots.stored uv known
    exact ⟨payload, by simpa only [framed.values] using stored, role⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem traversal_length (checkEmpty : Bool) (r n p h k : Nat)
    (inputs : List (Node × List Suspended)) (initialCaller caller : Caller width)
    (initial after : Cached) (initialQueries queries : Queries) (fragments : List Fragment)
    (trace : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Trace checkEmpty r n p h k inputs initialCaller initial initialQueries
      fragments caller after queries) : fragments.length = inputs.length := by
  induction trace with
  | nil => rfl
  | cons _head _tail ih => exact congrArg Nat.succ ih

/-- One current parent packet derives its exact finalizer and complete recording return. -/
theorem parent_callback_roles
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (target : Nat) (selected : marked target)
    (node : Option Nat) (targetScs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (checkEmpty : Bool) (r n p h k start : Nat) (scs : List Suspended)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (initialCaller caller : Caller width) (initial childrenAfter : Cached)
    (initialQueries : Queries) (memos : Memos) (fragments : List Fragment)
    (traversed : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Trace checkEmpty r n p h k
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
      initialCaller initial initialQueries fragments caller childrenAfter memos.query)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap childrenAfter.core marked)
    (stored : childrenAfter.core.values[target]? = some (.unenumerated node targetScs))
    (history : ∀ child ∈ fragments, PendingFragment childrenAfter.core child ∧
      FragmentAvoid childrenAfter.core.representatives target child)
    (seed : Seed) (packet : Packet formulas solver inventory caller memos metadata childrenAfter)
    (allocated : FragmentBound childrenAfter.core.counter (.node edge.entry.key.symbol fragments))
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (roots : Nat → Nat) (finalizeFuel : Nat) (before : Cached)
      (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      ((∀ extra, SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
        (finalizeFuel + extra) target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter) = some before) ∧
      ExceptT.run (SourcePruningEnumerationFinalize.finish target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core) =
        [.ok ((.node edge.entry.key.symbol fragments), before.core)] ∧
      before.core = {(SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core with
        values := childrenAfter.core.values.set target (.enumerated (.node edge.entry.key.symbol fragments)),
        expansionAncestry := []} ∧
      before.core.values[target]? = some (.enumerated (.node edge.entry.key.symbol fragments)) ∧
      before.expandable = (fun slot => if slot = target then false else childrenAfter.expandable slot) ∧
      before.waiting = EnumerationCanonicalWaiting.count roots (-1) (EnumerationSchedule.references
        (.unenumerated node targetScs : EnumerationState.UVarValue Symbol)) childrenAfter.waiting ∧
      Roots before.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) ∧
      StorageValid before.core ∧ SourcePruningEnumerationObservation.PendingRealized caller.checked.native.machine.heap before.core ∧
      (Safe (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core →
        IsRoot childrenAfter.core.representatives target → Safe before.core)) ∧
      Packet formulas solver inventory caller memos metadata before ∧
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata target (.inl (.node edge.entry.key.symbol fragments)) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments))) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments)) before.core) = [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → HookResult)
            stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (fuel + extra) metadata target (.node edge.entry.key.symbol fragments) caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      FragmentRoles literal marked (.node edge.entry.key.symbol fragments) ∧
      ProgramSlots valid literal caller.checked.native.machine.heap before.core marked ∧
      ProgramSlots valid literal caller.checked.native.machine.heap after marked := by
  let parent : Fragment := .node edge.entry.key.symbol fragments
  let prepared := SelectedEdge.finish residual parent childrenAfter
  have preparedCounter : prepared.core.counter = childrenAfter.core.counter := rfl
  have length : fragments.length = edge.children.length := by
    have count := traversal_length checkEmpty r n p h k _ initialCaller caller initial childrenAfter
      initialQueries memos.query fragments traversed
    simpa only [SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using count
  have parentRoles : FragmentRoles literal marked parent :=
    assembled_roles valid marked edge fields fragments length childrenRoles
  have preparedSafe : Safe prepared.core := SelectedEdge.finish_safe residual parent childrenAfter packet.safe allocated
  obtain ⟨roots, paths, _oldStorage, realized, counts, flags⟩ := packet.valid
  obtain ⟨finalizeFuel, before, running, raw, core, finalStored, finalFlag, finalWaiting,
    finalPaths, finalCounts, finalFlags, finalStorage, finalRealized, safeFinish⟩ :=
    SourcePruningEnumerationFinalize.complete caller.checked.native.machine.heap prepared target parent
      (.unenumerated node targetScs) stored roots paths counts flags preparedSafe.1 allocated realized
  have beforeCounter : before.core.counter = childrenAfter.core.counter := by
    rw [core]
    exact preparedCounter
  have resetSlots : ProgramSlots valid literal caller.checked.native.machine.heap
      {prepared.core with expansionAncestry := []} marked :=
    ⟨slots.bounded, slots.roots, slots.incoming, slots.stored⟩
  have written : Success (setValue target (.enumerated parent))
      {prepared.core with expansionAncestry := []} () before.core :=
    (EnumerationDriver.modify_success _ _ _).mpr core
  have beforeSlots := (SourceSynthesisProgramFragmentWrite.setValue_program_slots valid literal
    caller.checked.native.machine.heap _ before.core marked resetSlots target selected parent parentRoles written).2
  have pendingBefore := EnumerationReferences.setValue_pending target parent
    {prepared.core with expansionAncestry := []} before.core packet.pending (slots.incoming target selected) written
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  have preparedOrder : EnumerationOrder.Stratified prepared.core level frontier :=
    ⟨ordered.classes, ordered.expanded, ordered.pending⟩
  have parentPending : PendingFragment prepared.core parent :=
    pendingFragment_node prepared.core edge.entry.key.symbol fragments (fun child member => (history child member).1)
  have parentSeparate : FragmentAvoid prepared.core.representatives target parent := by
    intro uv hole
    change HasHole (.node edge.entry.key.symbol fragments) uv at hole
    cases hole with
    | child _ _ child _ member below => exact (history child member).2 uv below
  obtain ⟨nextLevel, nextOrder⟩ := EnumerationOrder.write_stratified prepared.core preparedSafe level frontier
    target preparedOrder node targetScs stored parent parentPending parentSeparate
  have finalOrder : EnumerationOrder.Stratified before.core nextLevel (frontier + 1) := by
    rw [core]
    exact EnumerationOrder.stratified_ancestry _ [] nextLevel (frontier + 1) nextOrder
  have beforePacket : Packet formulas solver inventory caller memos metadata before :=
    ⟨packet.context, safeFinish preparedSafe (slots.roots target selected), pendingBefore,
      ⟨roots, finalPaths, finalStorage, finalRealized, finalCounts, finalFlags⟩,
      ⟨nextLevel, frontier + 1, finalOrder⟩, by simpa only [beforeCounter] using packet.bounded⟩
  have allocatedBefore : FragmentBound before.core.counter parent := by
    change FragmentBound before.core.counter (.node edge.entry.key.symbol fragments)
    rw [beforeCounter]
    exact allocated
  obtain ⟨fuel, result, after, callback⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver inventory
      graph templates metadata target parent caller memos before seed beforePacket allocatedBefore bounded known
  have afterSlots := slots_frame valid marked caller.checked.native.machine.heap before.core after
    callback.2.2.1 beforeSlots
  exact ⟨roots, finalizeFuel, before, fuel, result, after,
    ⟨running, raw, core, finalStored, finalFlag, finalWaiting, finalPaths, finalCounts,
      finalFlags, finalStorage, finalRealized, safeFinish⟩,
    beforePacket, callback, parentRoles, beforeSlots, afterSlots⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- Ordered child roles determine the same assembled Program fragment. -/
theorem fragment_roles_of_children (valid : Constraint → Prop) (marked : Nat → Prop)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (fragments : List Fragment) (length : fragments.length = edge.children.length)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child) :
    FragmentRoles literal marked (.node edge.entry.key.symbol fragments) := by
  exact assembled_roles valid marked edge fields fragments length childrenRoles

end MicroCFTA.SourceSynthesisProgramParentCallbackRoles
