import MicroCFTA.SourcePruningEnumerationSharedEagerChildren
import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation
import MicroCFTA.SourcePruningEnumerationOwnChildModelProgress
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.EnumerationSemantics
import MicroCFTA.EnumerationStratifiedTransport

/-!
# Resources and a model for an actual nullary eager row

The current accepted row supplies its actual own-class prefix.
No child visitor runs. The native caller and full memos stay the same.
Captured-target finalization and consumer preservation remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEagerNullaryResources
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation SourcePruningEnumerationOrigins
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedChildVisitors (visitSelected)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
universe u v
variable {Typing : Type} {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Fold" => NativeContinuations.Result Output Reason width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation width → Option Cached → Fold) → Fold
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A nullary row retains its actual prefix, packet, native resources and accepted model. -/
theorem visitSelected_nullary_model_packet
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : Edge) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry rows depth free))
    (parentClosed : free = []) (selected : edge ∈ rows) (nullary : edge.children = [])
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol)
    (term whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc)
    (old : AssignmentOrigins whole before.core.counter assignment) (origin : Origin whole term) :
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint)
      (action : EnumerateM Symbol Constraint
        (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint))
      (own after : Cached) (extended : Nat → Term Symbol),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧ arityAllows edge.children.length scs = true ∧
      SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol, [], residual), own)] ∧
      ExceptT.run (action before.core) = [.ok ((edge.entry.key.symbol, [], residual), own.core)] ∧
      own.core = suspendedState tries.length before.core ∧
      after = SelectedEdge.finish residual (.node edge.entry.key.symbol []) own ∧
      (∀ (visit : Visitor) (consume : Receipt width → Fold),
        visitSelected visit consume scs edge caller before memos.query =
          consume (.complete (.node edge.entry.key.symbol []) caller memos.query after)) ∧
      Packet formulas solver inventory caller memos metadata after ∧
      Post formulas solver inventory caller caller memos ∧ Fits seed.2 caller.checked ∧
      Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      before.core.counter ≤ after.core.counter ∧ after.core.counter = before.core.counter + tries.length ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel frontier) ∧
      FragmentBound after.core.counter (.node edge.entry.key.symbol []) ∧
      PendingFragment after.core (.node edge.entry.key.symbol []) ∧ InputsPending after.core scs ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        extended before.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        extended after.core ∧
      Fragments.fill extended (.node edge.entry.key.symbol []) = term ∧
      AssignmentOrigins whole after.core.counter extended ∧
      ∀ sc ∈ scs, Suspended.Holds extended term sc := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨tries, residual, terms, admission, action, own, ownPacket,
    extended, agree, beforeModel, ownModel, combinedHeld, _childModels,
    _ownCost, ownOrigins, _childOrigins⟩ :=
    SourcePruningEnumerationOwnChildModelProgress.accepted_own_children_origins
      formulas solver inventory caller before parentEntry rows depth free edge scs roots memos
      packet.context parentAvailable parentClosed selected packet.safe realized paths counts flags
      bounded pending ambient assignment term satisfied accepted inherited whole old origin
  obtain ⟨projected, validTries, termShape, _acceptedChildren, lengths,
    allowed, _ownEqualities, residualHeld⟩ := admission
  have termsNil : terms = [] := by
    cases terms with
    | nil => rfl
    | cons first rest =>
        simp only [nullary, List.length_nil, List.length_cons] at lengths
        omega
  subst terms
  obtain ⟨sourcePrepared, ownRun, rawRun, ownCore, ownCounter, _ownForest,
    ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending,
    _genuine, _ownProtects⟩ := ownPacket
  have emptyInputs : SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries = [] := by
    simp [SourcePruningEnumerationEdgeInputs.children, nullary]
  have actualOwn : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, [], residual), own)] := by
    simpa only [emptyInputs, List.map_nil] using ownRun
  have actualRaw : ExceptT.run (action before.core) =
      [.ok ((edge.entry.key.symbol, [], residual), own.core)] := by
    simpa only [emptyInputs, List.map_nil] using rawRun
  let fragment : Fragment := .node edge.entry.key.symbol []
  let after := SelectedEdge.finish residual fragment own
  have actualVisit (visit : Visitor) (consume : Receipt width → Fold) :
      visitSelected visit consume scs edge caller before memos.query =
        consume (.complete fragment caller memos.query after) := by
    rw [visitSelected, actualOwn]
    rfl
  have ownFragmentBound : FragmentBound own.core.counter fragment := by trivial
  have afterSafe : Safe after.core :=
    SelectedEdge.finish_safe residual fragment own ownSafe ownFragmentBound
  have afterCounter : after.core.counter = before.core.counter + tries.length := by
    change own.core.counter = before.core.counter + tries.length
    exact ownCounter
  have growth : before.core.counter ≤ after.core.counter := by
    rw [afterCounter]
    omega
  have residualRun : Success (recordResidual residual fragment) own.core () after.core := by
    rw [Success, SelectedEdge.finish_raw]
    simp [after]
  have ownOrigin : EnumeratedOrigin before.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length before.core
  have fullOrigin : EnumeratedOrigin before.core after.core :=
    ownOrigin.trans (recordResidual_origin residual fragment own.core after.core residualRun)
  have protects (held : Nat) (inside : held < before.core.counter)
      (root : IsRoot before.core.representatives held) :
      EnumerationDriver.Protected held before.core after.core := by
    have ownProtected : EnumerationDriver.Protected held before.core own.core := by
      rw [ownCore]
      exact EnumerationDriver.suspension_protected held tries.length before.core packet.safe inside root
    exact ownProtected.trans (SelectedEdge.finish_protected residual fragment own held ownProtected.root)
  have protectsEnumerated (held : Nat) (storedFragment : Fragment)
      (stored : before.core.values[held]? = some (.enumerated storedFragment)) :
      EnumerationDriver.Protected held before.core after.core := by
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment stored
    exact protects held inside root
  have ordered (level : Nat → Nat) (frontier : Nat)
      (originalOrder : EnumerationOrder.Stratified before.core level frontier) :
      ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel frontier :=
    EnumerationOrder.stratified_preserved before.core after.core afterSafe level frontier
      originalOrder fullOrigin protectsEnumerated
  have afterPending : EnumerationReferences.PendingReferences after.core := by
    intro held storedFragment stored
    have previous := fullOrigin held storedFragment stored
    have ownAllowed : EnumerationReferences.ReferencesAllowed
        (fun uv => ¬UnionFind.SameClass before.core.representatives held uv) own.core := by
      rw [ownCore]
      exact EnumerationReferences.suspension_allowed _ tries.length before.core
        (packet.pending held storedFragment previous)
    have finalAllowed := EnumerationReferences.recordResidual_allowed _ residual fragment
      own.core after.core ownAllowed residualRun
    intro value member sc listed related
    exact finalAllowed value member sc listed (((protectsEnumerated held storedFragment previous).classes sc.var).mp related)
  have afterInputs : InputsPending after.core scs := by
    intro held storedFragment stored
    have previous := fullOrigin held storedFragment stored
    exact (protectsEnumerated held storedFragment previous).avoids scs (pending held storedFragment previous)
  have afterPacket : Packet formulas solver inventory caller memos metadata after := by
    refine ⟨packet.context, afterSafe, afterPending,
      ⟨roots, ownPaths, afterSafe.1, ownRealized, ownCounts, ownFlags⟩, ?_, ?_⟩
    · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
      obtain ⟨nextLevel, nextOrder⟩ := ordered level frontier oldOrder
      exact ⟨nextLevel, frontier, nextOrder⟩
    · intro group member entry listed
      exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
  have filled : Fragments.fill extended fragment = term := by
    rw [show fragment = (.node edge.entry.key.symbol [] : Fragment) from rfl, Fragments.fill]
    exact termShape.symm
  have afterModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended after.core :=
    (EnumerationSemantics.recordResidual_assignment _ _ extended residual fragment
      own.core after.core residualRun).mpr ⟨ownModel, by simpa only [filled] using residualHeld⟩
  have fragmentBound : FragmentBound after.core.counter fragment := by trivial
  have fragmentPending : PendingFragment after.core fragment :=
    pendingFragment_node after.core edge.entry.key.symbol [] (by intro child member; cases member)
  have afterOrigins : AssignmentOrigins whole after.core.counter extended := ownOrigins
  refine ⟨tries, residual, action, own, after, extended, projected, validTries, allowed,
    sourcePrepared, actualOwn, actualRaw, ownCore, rfl, actualVisit, afterPacket,
    Post.refl packet.context, fits, known, growth, afterCounter, fullOrigin, protects,
    ordered, fragmentBound, fragmentPending, afterInputs, agree, beforeModel, afterModel,
    filled, afterOrigins, ?_⟩
  intro sc member
  exact combinedHeld sc (List.mem_append.mpr (.inl member))

end MicroCFTA.SourcePruningEnumerationSharedEagerNullaryResources
