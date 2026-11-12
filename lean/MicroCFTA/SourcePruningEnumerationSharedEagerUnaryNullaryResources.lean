import MicroCFTA.SourcePruningEnumerationSharedEagerNullaryResources

/-!
# One actual ordinary descent to a singleton nullary row

Both own-class prefixes and residual updates keep the native state.
One final assignment models the parent and child packets.
The actual consumer result keeps its endpoint and receives the inner receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEagerUnaryNullaryResources
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation SourcePruningEnumerationOrigins
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild ordinaryNonterminal consumeSelected)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "OwnAction" => EnumerateM Symbol Constraint
  (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint)
universe u v
variable {Typing : Type} {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Fold" => NativeContinuations.Result Output Reason width
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem suspension_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos) (metadata : Metadata Typing)
    (before own : Cached) (count : Nat) (packet : Packet formulas solver inventory caller memos metadata before)
    (core : own.core = suspendedState count before.core) (growth : before.core.counter ≤ own.core.counter)
    (safe : Safe own.core) (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller own) :
    Packet formulas solver inventory caller memos metadata own ∧ EnumeratedOrigin before.core own.core ∧
    (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      EnumerationDriver.Protected held before.core own.core) ∧
    (∀ level bound, EnumerationOrder.Stratified before.core level bound →
      ∃ nextLevel, EnumerationOrder.Stratified own.core nextLevel bound) := by
  have origin : EnumeratedOrigin before.core own.core := by rw [core]; exact suspension_origin count before.core
  have protects (held : Nat) (inside : held < before.core.counter) (root : IsRoot before.core.representatives held) :
      EnumerationDriver.Protected held before.core own.core := by
    rw [core]
    exact EnumerationDriver.suspension_protected held count before.core packet.safe inside root
  have enumProtects (held : Nat) (fragment : Fragment) (stored : before.core.values[held]? = some (.enumerated fragment)) :
      EnumerationDriver.Protected held before.core own.core := by
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held fragment stored
    exact protects held inside root
  have ordered (level : Nat → Nat) (bound : Nat) (oldOrder : EnumerationOrder.Stratified before.core level bound) :
      ∃ nextLevel, EnumerationOrder.Stratified own.core nextLevel bound :=
    EnumerationOrder.stratified_preserved before.core own.core safe level bound oldOrder origin enumProtects
  have pending : EnumerationReferences.PendingReferences own.core := by
    intro held fragment stored
    have previous := origin held fragment stored
    have allowed : EnumerationReferences.ReferencesAllowed
        (fun uv => ¬UnionFind.SameClass before.core.representatives held uv) own.core := by
      rw [core]
      exact EnumerationReferences.suspension_allowed _ count before.core (packet.pending held fragment previous)
    intro value member sc listed related
    exact allowed value member sc listed (((enumProtects held fragment previous).classes sc.var).mp related)
  refine ⟨⟨packet.context, safe, pending, valid, ?_, ?_⟩, origin, protects, ordered⟩
  · obtain ⟨level, bound, oldOrder⟩ := packet.ordered
    obtain ⟨nextLevel, nextOrder⟩ := ordered level bound oldOrder
    exact ⟨nextLevel, bound, nextOrder⟩
  · intro group member entry listed
    exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth

/-- One ordinary child retains both actual prefixes, coupled models and the full consumer result. -/
theorem visitSelected_unary_nullary_model_packet
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : Edge) (scs : List Suspended) (child : Node)
    (childEntry : Cache.Interned InternedBinderProtocol.NodeKey) (leaf : Edge)
    (childDepth : Nat) (childFree : List InternedBinderProtocol.Reference) (edgesOf : Node → List Edge)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry rows depth free))
    (parentClosed : free = []) (selected : edge ∈ rows) (unary : edge.children = [child])
    (childShape : child = .node childEntry [leaf] childDepth childFree)
    (leafNullary : leaf.children = []) (selector : edgesOf child = [leaf])
    (ordinary : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ordinaryNonterminal (descendScs 0 scs ++ descendScs 0 (suspendedVars before.core.counter tries)) child = true)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol) (term whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc)
    (old : AssignmentOrigins whole before.core.counter assignment) (origin : Origin whole term) :
    ∃ (tries childTries : List EqualityTrie.Trie) (residual childResidual : Option Constraint)
      (action childAction : OwnAction) (own childOwn childAfter after : Cached)
      (bucket : List Suspended) (childTerm : Term Symbol) (extended : Nat → Term Symbol),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      SourcePruningEnumerationConstraint.project leaf.entry.key.constraint = some (childTries, childResidual) ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧ (∀ trie ∈ childTries, EqualityTrie.Valid trie) ∧
      arityAllows edge.children.length scs = true ∧ arityAllows leaf.children.length bucket = true ∧
      bucket = descendScs 0 scs ++ descendScs 0 (suspendedVars before.core.counter tries) ∧
      SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol,
          [(child, bucket, SourcePruningEnumerationShallowChild.prepareChild bucket child)], residual), own)] ∧
      ExceptT.run (action before.core) = [.ok ((edge.entry.key.symbol,
        [(child, bucket, SourcePruningEnumerationShallowChild.prepareChild bucket child)], residual), own.core)] ∧
      own.core = suspendedState tries.length before.core ∧
      SourcePruningEnumerationEdgePrefix.prepare bucket leaf = some childAction ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket leaf own =
        some [((leaf.entry.key.symbol, [], childResidual), childOwn)] ∧
      ExceptT.run (childAction own.core) = [.ok ((leaf.entry.key.symbol, [], childResidual), childOwn.core)] ∧
      childOwn.core = suspendedState childTries.length own.core ∧
      childAfter = SelectedEdge.finish childResidual (.node leaf.entry.key.symbol []) childOwn ∧
      after = SelectedEdge.finish residual (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) childAfter ∧
      Packet formulas solver inventory caller memos metadata own ∧
      Packet formulas solver inventory caller memos metadata childAfter ∧
      Packet formulas solver inventory caller memos metadata after ∧
      Post formulas solver inventory caller caller memos ∧ Fits seed.2 caller.checked ∧
      Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      after.core.counter = before.core.counter + tries.length + childTries.length ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ level bound, EnumerationOrder.Stratified before.core level bound →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel bound) ∧
      FragmentBound after.core.counter (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) ∧
      PendingFragment after.core (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) ∧ InputsPending after.core scs ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended before.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended own.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended childAfter.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended after.core ∧
      Fragments.fill extended (.node leaf.entry.key.symbol []) = childTerm ∧
      Fragments.fill extended (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) = term ∧
      AssignmentOrigins whole after.core.counter extended ∧
      (∀ sc ∈ scs, Suspended.Holds extended term sc) ∧
      ∀ checkEmpty r n p h k (consume : SelectedEdge.Result width → Fold),
        visitSelected (eagerChild checkEmpty r n p h k edgesOf) consume scs edge caller before memos.query =
          match consume (.complete (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) caller memos.query after) with
          | .complete processed outputs finalCaller finalQueries =>
              .complete (.complete (.node leaf.entry.key.symbol []) caller memos.query childAfter :: processed) outputs finalCaller finalQueries
          | .stopped processed outputs current =>
              .stopped (.complete (.node leaf.entry.key.symbol []) caller memos.query childAfter :: processed) outputs current := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨tries, residual, terms, admission, action, own, ownPacket, ownAssignment,
    ownAgree, _ownBeforeModel, ownModel, _combinedHeld, childModels, _ownCost, ownOrigins, termOrigins⟩ :=
    SourcePruningEnumerationOwnChildModelProgress.accepted_own_children_origins formulas solver inventory caller before
      parentEntry rows depth free edge scs roots memos packet.context parentAvailable parentClosed selected packet.safe
      realized paths counts flags bounded pending ambient assignment term satisfied accepted inherited whole old origin
  obtain ⟨projected, validTries, termShape, _acceptedChildren, _lengths, allowed, _equalities, residualHeld⟩ := admission
  obtain ⟨sourcePrepared, ownRun, rawRun, ownCore, ownCounter, _ownForest, ownSafe, ownPaths,
    ownRealized, ownCounts, ownFlags, _combinedPending, genuine, _ownProtects⟩ := ownPacket
  let bucket := descendScs 0 scs ++ descendScs 0 (suspendedVars before.core.counter tries)
  have inputsSame : SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries = [(child, bucket)] := by
    simp [SourcePruningEnumerationEdgeInputs.children, unary, bucket]
  have member : (child, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries := by
    rw [inputsSame]; exact List.mem_cons_self
  obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ := genuine child bucket member
  have ownGrowth : before.core.counter ≤ own.core.counter := by rw [ownCounter]; omega
  obtain ⟨ownedPacket, ownOrigin, ownProtects, ownOrder⟩ := suspension_packet formulas solver inventory caller memos metadata
    before own tries.length packet ownCore ownGrowth ownSafe ⟨roots, ownPaths, ownSafe.1, ownRealized, ownCounts, ownFlags⟩
  obtain ⟨childTerm, termsSame, childAccepted, childHeld⟩ : ∃ childTerm, terms = [childTerm] ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient child childTerm ∧
      ∀ sc ∈ bucket, Suspended.Holds ownAssignment childTerm sc := by
    rw [inputsSame] at childModels
    cases childModels with
    | cons head tail => cases tail; exact ⟨_, rfl, head.1, head.2⟩
  have leafAccepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient leaf childTerm := by
    rw [childShape, InternedGuardedLanguage.meaning] at childAccepted
    obtain ⟨chosen, accepts⟩ := childAccepted
    have same : chosen.val = leaf := List.mem_singleton.mp chosen.property
    simpa only [same] using accepts
  have storedAvailable : Available caller.checked.native.machine.heap (.node childEntry [leaf] childDepth childFree) := by
    simpa only [childShape] using childAvailable
  have storedClosed : childFree = [] := by
    rw [childShape] at childClosed
    exact childClosed
  have childTermOrigin : Origin whole childTerm := termOrigins childTerm (by rw [termsSame]; exact List.mem_cons_self)
  obtain ⟨childTries, childResidual, childAction, childOwn, childAfter, extended, childProjected, childValid,
    childAllowed, childPrepared, childOwnRun, childRaw, childCore, childFinish, childVisit, childPacket, childPost,
    childFits, childHeap, _childGrowth, childCounter, childOrigin, childProtects, childOrder, childBound,
    childFragmentPending, _childInputs, childAgree, childBeforeModel, childAfterModel, childFilled, childOrigins, _childHeldAfter⟩ :=
    SourcePruningEnumerationSharedEagerNullaryResources.visitSelected_nullary_model_packet (Output := Output) (Reason := Reason)
      seed formulas solver inventory caller memos metadata own childEntry [leaf] childDepth childFree leaf bucket ownedPacket
      storedAvailable storedClosed List.mem_cons_self leafNullary childBounded childPending fits known ambient ownAssignment
      childTerm whole ownModel leafAccepted childHeld ownOrigins childTermOrigin
  have actualOwn : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((edge.entry.key.symbol, [(child, bucket, SourcePruningEnumerationShallowChild.prepareChild bucket child)], residual), own)] := by
    simpa only [inputsSame, List.map_cons, List.map_nil] using ownRun
  have actualRaw : ExceptT.run (action before.core) = [.ok ((edge.entry.key.symbol,
      [(child, bucket, SourcePruningEnumerationShallowChild.prepareChild bucket child)], residual), own.core)] := by
    simpa only [inputsSame, List.map_cons, List.map_nil] using rawRun
  let childFragment : Fragment := .node leaf.entry.key.symbol []
  let fragment : Fragment := .node edge.entry.key.symbol [childFragment]
  let after := SelectedEdge.finish residual fragment childAfter
  have parentBound : FragmentBound childAfter.core.counter fragment := ⟨childBound, trivial⟩
  have afterSafe : Safe after.core := SelectedEdge.finish_safe residual fragment childAfter childPacket.safe parentBound
  have afterPacket : Packet formulas solver inventory caller memos metadata after := by
    obtain ⟨childRoots, childPaths, _childStorage, childRealized, childCounts, childFlags⟩ := childPacket.valid
    obtain ⟨childLevel, childFrontier, childStratified⟩ := childPacket.ordered
    exact ⟨childPacket.context, afterSafe, childPacket.pending,
      ⟨childRoots, childPaths, afterSafe.1, childRealized, childCounts, childFlags⟩,
      ⟨childLevel, childFrontier, childStratified.classes, childStratified.expanded, childStratified.pending⟩,
      childPacket.bounded⟩
  have counter : after.core.counter = before.core.counter + tries.length + childTries.length := by
    change childAfter.core.counter = before.core.counter + tries.length + childTries.length
    rw [childCounter, ownCounter]
  have residualRun : Success (recordResidual residual fragment) childAfter.core () after.core := by
    rw [Success, SelectedEdge.finish_raw]; simp [after]
  have fullOrigin : EnumeratedOrigin before.core after.core :=
    ownOrigin.trans (childOrigin.trans (recordResidual_origin residual fragment childAfter.core after.core residualRun))
  have protects (held : Nat) (inside : held < before.core.counter) (root : IsRoot before.core.representatives held) :
      EnumerationDriver.Protected held before.core after.core := by
    have first := ownProtects held inside root
    have second := childProtects held (Nat.lt_of_lt_of_le inside ownGrowth) first.root
    exact first.trans (second.trans (SelectedEdge.finish_protected residual fragment childAfter held second.root))
  have ordered (level : Nat → Nat) (bound : Nat) (oldOrder : EnumerationOrder.Stratified before.core level bound) :
      ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel bound := by
    obtain ⟨ownLevel, ownedOrder⟩ := ownOrder level bound oldOrder
    obtain ⟨nextLevel, nextOrder⟩ := childOrder ownLevel bound ownedOrder
    exact ⟨nextLevel, nextOrder.classes, nextOrder.expanded, nextOrder.pending⟩
  have afterInputs : InputsPending after.core scs := by
    intro held storedFragment stored
    have previous := fullOrigin held storedFragment stored
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment previous
    exact (protects held inside root).avoids scs (pending held storedFragment previous)
  have agree : ∀ uv < before.core.counter, extended uv = assignment uv :=
    fun uv inside => (childAgree uv (Nat.lt_of_lt_of_le inside ownGrowth)).trans (ownAgree uv inside)
  have beforeModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended before.core :=
    (state_assignment_congr _ _ before.core packet.safe.1 extended assignment agree).mpr satisfied
  have filled : Fragments.fill extended fragment = term := by
    rw [show fragment = (.node edge.entry.key.symbol [childFragment] : Fragment) from rfl, Fragments.fill]
    change Term.node edge.entry.key.symbol [Fragments.fill extended childFragment] = term
    rw [childFilled, ← termsSame]
    exact termShape.symm
  have afterModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended after.core :=
    (EnumerationSemantics.recordResidual_assignment _ _ extended residual fragment childAfter.core after.core residualRun).mpr
      ⟨childAfterModel, by simpa only [filled] using residualHeld⟩
  have fragmentPending : PendingFragment after.core fragment := pendingFragment_node after.core _ [childFragment] (by
    intro current listed; obtain rfl := List.mem_singleton.mp listed; exact childFragmentPending)
  refine ⟨tries, childTries, residual, childResidual, action, childAction, own, childOwn, childAfter, after,
    bucket, childTerm, extended, projected, childProjected, validTries, childValid, allowed, childAllowed, rfl,
    sourcePrepared, actualOwn, actualRaw, ownCore, childPrepared, childOwnRun, childRaw, childCore, childFinish, rfl,
    ownedPacket, childPacket, afterPacket, childPost, childFits, childHeap, counter, fullOrigin, protects, ordered,
    parentBound, fragmentPending, afterInputs, agree, beforeModel, childBeforeModel, childAfterModel, afterModel,
    childFilled, filled, childOrigins, ?_, ?_⟩
  · intro sc present path represented
    rw [agree sc.var (bounded sc present)]
    exact inherited sc present path represented
  · intro checkEmpty r n p h k consume
    simp only [visitSelected, actualOwn, List.map_cons, List.map_nil, visitChildren]
    rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary checkEmpty r n p h k edgesOf bucket child caller own memos.query _ _
      (ordinary tries residual projected), selector, SourcePruningEnumerationSharedBranching.scan, childVisit]
    cases outcome : consume (.complete fragment caller memos.query after) <;>
      dsimp only [fragment, childFragment, after] at outcome <;>
      simp only [consumeSelected, outcome, SourcePruningEnumerationSharedBranching.scan, List.append_nil]

end MicroCFTA.SourcePruningEnumerationSharedEagerUnaryNullaryResources
