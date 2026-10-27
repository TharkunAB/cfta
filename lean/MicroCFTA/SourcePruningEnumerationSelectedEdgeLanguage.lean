import MicroCFTA.SourcePruningEnumerationSelectedEdgeStableLanguage

/-!
# Exact assignment language of actual completed selected edges

The original producer runs once and retains every runtime and history receipt.
A completed edge retains its actual ordered child fragments and full residual.
The semantic clause uses each child's effective stored suspended bucket.
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

/-- Retain the complete original packet and exact assignment language of its actual complete result. -/
theorem complete_with_fragments_semantics
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
    (ranges : Ranges checkEmpty scs edge caller before memos.query) :
    ∃ (r n p h k : Nat) (afterCaller : Caller width) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result width),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧ InputsPending after.core scs ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationReferences.IncomingAvoid held before.core →
        EnumerationReferences.IncomingAvoid held after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
          ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
            Avoids before.core.representatives held scs → FragmentAvoid after.core.representatives held fragment) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      (∀ fragment, result = .complete fragment afterCaller savedQueries after →
        ∃ childFragments : List Fragment,
          fragment = .node edge.entry.key.symbol childFragments ∧
          ∀ (ambient : InternedGuardedLanguage.Env Symbol)
            (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core ↔
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient caller.checked.native.machine.heap) residualMeaning assignment before.core ∧
              All₂ (fun (input : Node × List Suspended) (child : Fragment) =>
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                  ambient input.1 (Fragments.fill assignment child) ∧
                ∀ sc ∈ (match input.1 with
                  | .node _ _ _ _ => input.2
                  | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
                  Suspended.Holds assignment (Fragments.fill assignment child) sc)
                (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) childFragments ∧
              ResidualHolds residualMeaning residual (Fragments.fill assignment fragment)) := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
    afterFlags, origin, retained, protectedRoots, pendingHistory, incomingHistory, shape⟩ :=
      complete_with_fragments formulas solver inventory caller before checkEmpty parentEntry edges depth free
        edge scs roots memos initial parentAvailable parentClosed selected safe realized paths counts flags
        bounded pending allowed tries residual projected ranges
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
    afterFlags, origin, retained, protectedRoots, pendingHistory, incomingHistory, shape, ?_⟩
  intro fragment completed
  apply stable_complete_semantics formulas solver inventory caller before checkEmpty parentEntry edges depth free
    edge scs roots memos initial parentAvailable parentClosed selected safe realized paths counts flags
    bounded pending allowed tries residual projected ranges
  intro er en P H ek enoughP enoughH
  exact (running er en P H ek enoughP enoughH).trans completed

end MicroCFTA.SourcePruningEnumerationSelectedEdge
