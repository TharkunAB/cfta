import MicroCFTA.SourcePruningEnumerationCapturedEdgeResourceSoundness

/-!
# Resource soundness from actual diagonal completion

Original input resources supply independent sufficient execution bounds.
An actual stable diagonal family identifies the same completed result.
The current semantic gates remain explicit.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationValidity EnumerationSemantics EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original resources identify independent completion bounds at the same actual diagonal endpoint. -/
theorem stable_complete_of_diagonal_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
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
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 caller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller (bits + 2)}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extra,
      run checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some (.complete fragment afterCaller savedQueries after)) :
    ∃ r n p h k : Nat, ∀ er en P H ek, p ≤ P → h ≤ H →
      run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query =
        some (.complete fragment afterCaller savedQueries after) := by
  obtain ⟨r, n, p, h, k, reached, finished, saved, final, next, afterRoots, result,
      running, _post, _querySame, _growth, _paths, _storage, _realized, _counts, _flags,
      _origin, _pending, _protects, _pendingHistory, _shape, _returnedFits, _returnedKnown⟩ :=
    complete_resources seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry edges depth free
      edge roots memos initial ready stored decoded realized selected paths counts flags pending allowed
      tries residual projected fits reserved known
  let w := bound + r + n + p + h + k
  have rl : r ≤ w := by dsimp [w]; omega
  have nl : n ≤ w := by dsimp [w]; omega
  have pl : p ≤ w := by dsimp [w]; omega
  have hl : h ≤ w := by dsimp [w]; omega
  have kl : k ≤ w := by dsimp [w]; omega
  have produced : run checkEmpty w w w w w uv scs edge caller before memos.query = some result := by
    simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using
      running (w - r) (w - n) w w (w - k) pl hl
  have diagonal : run checkEmpty w w w w w uv scs edge caller before memos.query =
      some (.complete fragment afterCaller savedQueries after) := by
    simpa only [w, Nat.add_assoc] using observed (r + n + p + h + k)
  have same : result = .complete fragment afterCaller savedQueries after :=
    Option.some.inj (produced.symm.trans diagonal)
  exact ⟨r, n, p, h, k, by simpa only [same] using running⟩

/-- Actual diagonal completion accepts the captured term under the existing current semantic gates. -/
theorem diagonal_complete_sound_current_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
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
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 caller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller (bits + 2)}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extra,
      run checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some (.complete fragment afterCaller savedQueries after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
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
        ambient edge (assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) (assignment uv) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
      Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨r, n, p, h, k, running⟩ :=
    stable_complete_of_diagonal_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
      paths counts flags pending allowed tries residual projected fits reserved known observed
  exact stable_complete_sound_current_resources seed formulas solver inventory caller before checkEmpty uv handle scs
    parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
    paths counts flags pending allowed tries residual projected fits reserved known canonical nonterminal freshArity retained running

end MicroCFTA.SourcePruningEnumerationCapturedEdge
