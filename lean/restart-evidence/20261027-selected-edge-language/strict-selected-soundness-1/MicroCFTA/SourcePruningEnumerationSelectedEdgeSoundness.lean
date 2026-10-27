import MicroCFTA.SourcePruningEnumerationSelectedEdgeStableLanguage
import MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
import MicroCFTA.SourcePruningEnumerationEdgeChildLanguage

/-!
# Native language soundness of an actual completed selected edge

The actual runtime equivalence supplies the child and residual evidence.
Current annotation, arity, validity and retention gates remain explicit.
These gates are separate from the original completion admission.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A satisfying completed cache accepts its actual selected edge under the current semantic gates. -/
theorem stable_complete_sound
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : Ranges checkEmpty scs edge caller before memos.query)
    (annotated : SourceEqualityAnnotationHeap.Heap
      (fun guard => SourceEqualityGuardReadback.Cached guard.equalities)
      caller.checked.native.machine.heap)
    (inheritedValid : EnumerationSemantics.ValidSuspended scs)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
        .complete fragment afterCaller savedQueries after) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment after.core →
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (Fragments.fill assignment fragment) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) (Fragments.fill assignment fragment) ∧
      ∀ sc ∈ scs, Suspended.Holds assignment (Fragments.fill assignment fragment) sc := by
  obtain ⟨childFragments, shape, semantics⟩ :=
    stable_complete_semantics formulas solver inventory caller before checkEmpty parentEntry edges depth free
      edge scs roots memos initial parentAvailable parentClosed selected safe realized paths counts flags
      bounded pending allowed tries residual projected ranges observed
  obtain ⟨valid, guardMeaning⟩ := SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
    caller.checked.native.machine.heap parentEntry edges depth free edge initial.ready.semantic.ready
      annotated parentAvailable selected tries residual projected
  intro ambient assignment satisfied
  obtain ⟨beforeSatisfied, children, residualSatisfied⟩ :=
    (semantics ambient (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment).mp satisfied
  obtain ⟨forest, descendants⟩ := SourcePruningEnumerationEdgeChildLanguage.child_evidence
    (SourceEqualityPCSGuard.holds formulas solver) ambient assignment edge scs before.core.counter
      tries childFragments retained children
  obtain ⟨equalities, inherited⟩ := SourcePruningEnumerationEdgeChildLanguage.restrictions_from_children
    (SourceEqualityPCSGuard.holds formulas solver) ambient assignment edge scs before.core.counter
      tries childFragments forest descendants valid freshArity inheritedValid allowed nonterminal
  have filled : Fragments.fill assignment fragment =
      .node edge.entry.key.symbol (childFragments.map (Fragments.fill assignment)) := by
    rw [shape]
    rfl
  have guardAccepted : SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint
      (Fragments.fill assignment fragment) = true := by
    apply (guardMeaning formulas solver _).mpr
    exact ⟨by rw [filled]; exact equalities, residualSatisfied⟩
  have edgeAccepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
      ambient edge (Fragments.fill assignment fragment) := by
    cases edge with
    | mk entry values => exact ⟨childFragments.map (Fragments.fill assignment), filled, forest, guardAccepted⟩
  refine ⟨beforeSatisfied, edgeAccepted, ⟨⟨edge, selected⟩, edgeAccepted⟩, ?_⟩
  simpa only [filled] using inherited

end MicroCFTA.SourcePruningEnumerationSelectedEdge
