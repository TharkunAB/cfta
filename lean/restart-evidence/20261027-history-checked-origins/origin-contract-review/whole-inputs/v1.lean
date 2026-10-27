import MicroCFTA.SourceCurrentAllocatedParentEdge
import MicroCFTA.SourcePruningEnumerationOwnArity
import MicroCFTA.SourcePruningEnumerationHeadAdmission

/-!
# Projected arity from retained actual Parent construction receipts

The existing constructor receipt retains its actual checked guard and children.
Its returned native context supplies normalized projected equality classes.
The existing Parent receipt retains that constructor receipt in both branches.
Actual native Posts retain the same resident edge at a later selected head.
These results do not create missing origin history for an arbitrary Packet.
-/
namespace MicroCFTA.SourceCurrentAllocatedMkEdge
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual checked constructor receipt derives projected validity and fresh arity. -/
theorem Receipt.projected_arity
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Constraint)}
    {before after : SourceEqualityNativeDemand.State width} {result : EdgeValue Symbol Constraint}
    (receipt : Receipt formulas solver inventory symbol constraint children before result after)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project result.entry.key.constraint = some (tries, residual)) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows result.children.length (suspendedVars start tries) = true := by
  have cached := (receipt.ready.good.fields result.entry.key result receipt.resident).1
  have guardSame := receipt.guard
  have childrenSame := receipt.children
  cases keep : SourceEqualityMkEdgeAllocation.accepted (raw constraint) children.length with
  | false =>
      simp only [keep, Bool.false_eq_true, ↓reduceIte] at guardSame
      rw [guardSame] at projected
      have topProjection : SourcePruningEnumerationConstraint.project (top : Constraint) = some ([], none) := rfl
      rw [topProjection] at projected
      have triesSame : [] = tries := congrArg Prod.fst (Option.some.inj projected)
      subst tries
      exact ⟨by simp, fun _ => rfl⟩
  | true =>
      simp only [keep, ↓reduceIte] at guardSame childrenSame
      rw [guardSame] at cached projected
      have fits : SourceEqualityMkEdgeAllocation.fits children.length
          (SourceCompactGuards.sourceEqualities (raw constraint)) = true := by
        by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory (raw constraint) = true
        · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
            Bool.false_eq_true] at keep
        · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, Bool.false_eq_true,
            ↓reduceIte] using keep
      obtain ⟨classes, source, rootBounds⟩ := (SourceEqualityMkEdgeArity.fits_exact children.length
        (SourceCompactGuards.sourceEqualities (raw constraint))).mp fits
      obtain ⟨canonicalProjection, validTries, pathReadback, _meaning⟩ :=
        (source ▸ SourcePruningEnumerationConstraint.project_complete (raw constraint) cached)
      have triesSame : EnumerationEquality.readClasses classes = tries :=
        congrArg Prod.fst (Option.some.inj (canonicalProjection.symm.trans projected))
      refine ⟨?_, ?_⟩
      · rw [← triesSame]
        exact validTries
      · intro start
        rw [childrenSame, ← triesSame]
        apply (fresh_arity_iff children.length start (EnumerationEquality.readClasses classes)).mpr
        intro trie member index suffix path
        obtain ⟨paths, pathsMember, same⟩ := List.mem_map.mp member
        subst trie
        exact rootBounds paths pathsMember (index :: suffix)
          ((pathReadback paths pathsMember (index :: suffix)).mp path)

/-- The actual raw-rejection receipt supplies the empty own projection. -/
theorem RejectReceipt.projected_arity
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {before after : SourceEqualityNativeDemand.State width}
    {result : EdgeValue Symbol Constraint}
    (receipt : RejectReceipt formulas solver inventory symbol before result after)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project result.entry.key.constraint = some (tries, residual)) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows result.children.length (suspendedVars start tries) = true := by
  rw [receipt.guard] at projected
  have topProjection : SourcePruningEnumerationConstraint.project (top : Constraint) = some ([], none) := rfl
  rw [topProjection] at projected
  have triesSame : [] = tries := congrArg Prod.fst (Option.some.inj projected)
  subst tries
  exact ⟨by simp, fun _ => rfl⟩

end MicroCFTA.SourceCurrentAllocatedMkEdge

namespace MicroCFTA.SourceCurrentAllocatedParentEdge
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- The existing Parent construction field supplies arity without another original admission. -/
theorem Receipt.projected_arity
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {original : Constraint} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited : SourceEqualityConstraintAllocation.Value} {values : List (Value Symbol Constraint)}
    {before after : SourceEqualityNativeDemand.State width} {result : EdgeValue Symbol Constraint}
    {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
    {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Constraint} {final : EndpointMemoGateTrace.Memos}
    (receipt : Receipt formulas solver inventory symbol original loaded inherited values before result after
      fourth savedFourth memo saved final)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project result.entry.key.constraint = some (tries, residual)) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows result.children.length (suspendedVars start tries) = true := by
  rcases receipt.construction with rejected | ⟨_children, _middle, _length, built⟩
  · exact rejected.projected_arity tries residual projected
  · exact built.projected_arity tries residual projected

end MicroCFTA.SourceCurrentAllocatedParentEdge

namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A retained actual Parent receipt supplies this selected head's fresh own arity. -/
theorem CompletedHeadReceipt.freshArity_of_parent_construction
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : Cached} {checkEmpty : Bool} {uv : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {bound : Nat} {fragment : Fragments.Fragment Symbol}
    {reached : Caller (bits + 2)} {savedQueries : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached savedQueries after returnedInventory returnedMemos)
    {sourceInventory : Inventory} {symbol : Symbol} {original : Constraint}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {sourceInherited : SourceEqualityConstraintAllocation.Value} {values : List Node}
    {sourceBefore sourceAfter : SourceEqualityNativeDemand.State (bits + 2)}
    {builtEdge : EdgeValue Symbol Constraint}
    {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
    {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Constraint} {final : Memos}
    (origin : SourceCurrentAllocatedParentEdge.Receipt formulas solver sourceInventory symbol original loaded
      sourceInherited values sourceBefore builtEdge sourceAfter fourth savedFourth memo saved final)
    (originCaller : Caller (bits + 2))
    (originHeap : originCaller.checked.native.machine.heap = sourceAfter.native.machine.heap)
    (retained : Post formulas solver inventory originCaller caller memos)
    (sameIdentity : builtEdge.entry.identity = edge.entry.identity) :
    ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (suspendedVars before.core.counter tries) = true := by
  have kept : SourceEqualityRequiredCache.Keeps sourceAfter.native.machine.heap
      caller.checked.native.machine.heap := by
    rw [← originHeap]
    exact retained.effects.keeps
  have builtResident := InternedEdgeResidency.edge_grows sourceAfter.native.machine.heap
    caller.checked.native.machine.heap kept.growth builtEdge origin.resident
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := head.admission.packet.valid
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := head.admission.source
  obtain ⟨parent, parentLookup, available, _closed⟩ := realized uv handle scs stored
  have parentSame : parent = .node parentEntry edges depth free :=
    Option.some.inj (parentLookup.symm.trans decoded)
  subst parent
  have ready := head.admission.packet.context.ready.semantic.ready
  have selectedResident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap ready.semantic.1.normal.facts.linked
      (.node parentEntry edges depth free) available.resident edge selected
  have selectedSame := InternedEdgeResidency.edge_identity_unique caller.checked.native.machine.heap
    ready.semantic.1.normal.facts.coherent builtEdge edge builtResident selectedResident sameIdentity
  intro tries residual projected
  have originalProjected : SourcePruningEnumerationConstraint.project builtEdge.entry.key.constraint =
      some (tries, residual) := by simpa only [selectedSame] using projected
  have ownArity := (origin.projected_arity tries residual originalProjected).2
  simpa only [selectedSame] using ownArity before.core.counter

end MicroCFTA.SourcePruningEnumerationNativeHookResources
