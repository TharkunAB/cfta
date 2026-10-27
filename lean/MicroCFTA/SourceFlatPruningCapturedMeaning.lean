import MicroCFTA.SourceFlatPruningCapturedCompletion
import MicroCFTA.SourcePruningEnumerationCapturedEdgeSoundness
import MicroCFTA.EnumerationFlatSemantics

/-!
# Language meaning of actual flat captured completions

Original admission gives one bound before the flat cache is chosen.
An actual flat completion identifies the stable earlier completion.
Its assignment restores the original cache language at the original heap.
The semantic gates remain explicit.
-/
namespace MicroCFTA.SourceFlatPruningCapturedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual flat completion at the derived bound restores its original language under the semantic gates. -/
theorem complete_sound_current
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    ∃ bound : Nat, ∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
      ∀ (extra : Nat) (fragment : Fragment) (reached : Caller width)
        (saved : SourceEndpointMemo.Memos) (after : FlatCached),
      run checkEmpty (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller flat memos.query = some (.complete fragment reached saved after) →
      ∃ earlier : Cached,
        EnumerationFlatCached.Related after earlier ∧ Safe earlier.core ∧
        (∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          ∃ nextLevel, EnumerationOrder.Stratified earlier.core nextLevel (frontier + 1)) ∧
        ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
          EnumerationFlatState.Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient reached.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            assignment after.core →
          EnumerationFlatState.Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            assignment flat.core ∧
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient edge (assignment uv) ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient (.node parentEntry edges depth free) (assignment uv) ∧
          (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
          Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨r, n, p, h, k, earlierCaller, earlierAfter, earlierQueries, _final, _next, _afterRoots,
    result, ⟨running, _post, _querySame, _growth, _paths, _storage, _realized, _counts,
      _flags, _origin, _pending, _protects, _history, shape⟩, flatRunning⟩ :=
    SourceFlatPruningCapturedCompletion.complete_with_history formulas solver inventory caller before
      checkEmpty uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded
      realized selected paths counts flags pending allowed tries residual projected ranges
  let bound := r + n + p + h + k
  refine ⟨bound, ?_⟩
  intro flat related extra fragment reached saved after observed
  have enoughN : n ≤ bound + extra := by dsimp [bound]; omega
  have enoughP : p ≤ bound + extra := by dsimp [bound]; omega
  have enoughH : h ≤ bound + extra := by dsimp [bound]; omega
  obtain ⟨flatResult, actual, compared, _correct⟩ :=
    flatRunning flat related (bound + extra - n) (bound + extra) (bound + extra) enoughP enoughH
  rw [Nat.add_sub_of_le enoughN] at actual
  have same : flatResult = .complete fragment reached saved after := Option.some.inj (actual.symm.trans observed)
  subst flatResult
  rcases shape with ⟨earlierFragment, completed, safe, _bounded, _written, _ancestry, _root,
    _fragmentPending, ordered⟩ | ⟨fragments, outer, waiting, stopped⟩
  · rw [completed] at compared running
    obtain ⟨rfl, rfl, rfl, caches⟩ := compared
    refine ⟨earlierAfter, caches, safe, ordered, ?_⟩
    intro ambient assignment satisfies
    have earlierSatisfies := (EnumerationFlatState.related_satisfies caches.core _ _ assignment).mpr satisfies
    obtain ⟨original, edgeAccepted, parentAccepted, suspended, filled⟩ :=
      SourcePruningEnumerationCapturedEdge.stable_complete_sound_current formulas solver inventory caller before
        checkEmpty uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded
        realized selected paths counts flags pending allowed tries residual projected ranges canonical nonterminal
        freshArity retained running ambient assignment earlierSatisfies
    exact ⟨(EnumerationFlatState.related_satisfies related.core _ _ assignment).mp original,
      edgeAccepted, parentAccepted, suspended, filled⟩
  · rw [stopped] at compared
    cases compared

end MicroCFTA.SourceFlatPruningCapturedEdge
