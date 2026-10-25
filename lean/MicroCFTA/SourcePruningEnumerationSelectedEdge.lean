import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.SourcePruningEnumerationTraversalCompletion

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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

/-- Retain prefix rejection, unsupported preparation, stopped children and a completed edge. -/
inductive Result (width : Nat) where
  /-- The prefix does not supply the supported singleton packet. -/
  | unhandled
  /-- The arity check rejects before any child runs. -/
  | rejected (caller : Caller width) (queries : Queries) (after : Cached)
  /-- Retain the exact first stopping child observation and optional cache. -/
  | stopped (completedPrefix : List Fragment)
      (observation : SourcePruningEnumerationChildDispatch.Observation width) (candidate : Option Cached)
  /-- Every child succeeds and the edge residual is recorded. -/
  | complete (fragment : Fragment) (caller : Caller width) (queries : Queries) (after : Cached)

/-- Record the residual in the actual completed cache. -/
def finish (residual : Option Constraint) (fragment : Fragment) (before : Cached) : Cached :=
  EnumerationExpandableIndex.frame {before.core with obligations :=
    match residual with
    | none => before.core.obligations
    | some guard => (guard, fragment) :: before.core.obligations} before

/-- Residual recording has exactly the source action's successful singleton result. -/
theorem finish_raw (residual : Option Constraint) (fragment : Fragment) (before : Cached) :
    ExceptT.run (recordResidual residual fragment before.core) = [.ok ((), (finish residual fragment before).core)] := by
  cases residual <;> rfl

/-- A bounded completed fragment permits the exact residual update. -/
theorem finish_safe (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (safe : Safe before.core) (bounded : FragmentBound before.core.counter fragment) :
    Safe (finish residual fragment before).core := by
  apply (recordResidual_safe residual fragment before.core _ safe bounded ?_).1
  rw [Success, finish_raw]
  simp

/-- Residual recording retains every existing root, its stored value and its class. -/
theorem finish_protected (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (held : Nat) (root : IsRoot before.core.representatives held) :
    EnumerationDriver.Protected held before.core (finish residual fragment before).core :=
  ⟨rfl, root, fun _ => Iff.rfl⟩

private theorem node_bound (limit : Nat) (symbol : Symbol) (fragments : List Fragment)
    (bounded : ∀ fragment ∈ fragments, FragmentBound limit fragment) :
    FragmentBound limit (.node symbol fragments) := by
  induction fragments with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨bounded first (by simp), ih (fun fragment member => bounded fragment (by simp [member]))⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run the actual own-class prefix, ordered native children and final residual update. -/
noncomputable def run (checkEmpty : Bool) (r n p h k : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Result width :=
  match SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => .unhandled
  | some [] => .rejected caller queries before
  | some [((symbol, staged, residual), middle)] =>
      match SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
          (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
      | .stopped fragments observation candidate => .stopped fragments observation candidate
      | .complete fragments afterCaller saved after =>
          let fragment := Fragments.Fragment.node symbol fragments
          .complete fragment afterCaller saved (finish residual fragment after)
  | _ => .unhandled

/-- Numeric admission is required at the actual successful own-class prefix endpoint. -/
def Ranges (checkEmpty : Bool) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  ∀ symbol staged residual middle,
    SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)] →
    SourcePruningEnumerationTraversalCompletion.Ranges checkEmpty
      (staged.map (fun input => (input.1, input.2.1))) caller middle queries

/-- Arity rejection retains the original caller and cache without running a child. -/
theorem arity_rejected (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (rejected : arityAllows edge.children.length scs = false) :
    run checkEmpty r n p h k scs edge caller before queries = .rejected caller queries before := by
  simp only [run, SourcePruningEnumerationCachedOwn.prepare, rejected, Bool.false_eq_true, ↓reduceIte]

/-- Unsupported annotations retain the explicit prefix fallback. -/
theorem unsupported (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (allowed : arityAllows edge.children.length scs = true)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) :
    run checkEmpty r n p h k scs edge caller before queries = .unhandled := by
  simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]

/-- Every stopped child receipt retains its prefix, observation and optional cache. -/
theorem children_stopped (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (symbol : Symbol) (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (residual : Option Constraint) (middle : Cached) (fragments : List Fragment)
    (observation : SourcePruningEnumerationChildDispatch.Observation width) (candidate : Option Cached)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)])
    (stopped : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      (staged.map (fun input => (input.1, input.2.1))) caller middle queries =
        .stopped fragments observation candidate) :
    run checkEmpty r n p h k scs edge caller before queries = .stopped fragments observation candidate := by
  simp only [run, prepared, stopped]

/-- A selected supported edge derives native completion or its first valid child rejection. -/
theorem complete
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
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) := by
  obtain ⟨action, own, _prepared, ownRun, _raw, ownCore, ownCounter, _ownForest, ownSafe,
    ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, genuine, ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  have numeric : SourcePruningEnumerationTraversalCompletion.Ranges checkEmpty inputs caller own memos.query := by
    have admitted := ranges edge.entry.key.symbol _ residual own ownRun
    rwa [readback] at admitted
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots,
    childResult, childrenRun, post, querySame, growth, afterPaths, storage, afterRealized,
    afterCounts, afterFlags, origin, enumProtects, rootsProtects, fragmentBounds, shape⟩ :=
    SourcePruningEnumerationTraversalCompletion.complete formulas solver inventory caller own checkEmpty inputs roots memos
      initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine numeric
  have ownOrigin : EnumeratedOrigin before.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length before.core
  have fullOrigin := ownOrigin.trans origin
  have ownPending : InputsPending own.core scs := by
    intro held fragment stored
    have old := ownOrigin held fragment stored
    have frame := EnumerationDriver.suspension_protected held tries.length before.core safe
      (enumerated_root before.core safe held fragment old).1 (enumerated_root before.core safe held fragment old).2
    rw [← ownCore] at frame
    exact frame.avoids scs (pending held fragment old)
  have retained := SourcePruningEnumerationTraversalCompletion.retained_inputs own.core after.core scs
    ownPending origin enumProtects
  have protectedRoots : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core := by
    intro held inside root avoids
    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
    exact frame.trans (rootsProtects held (by omega) frame.root avoidsChildren)
  rcases shape with ⟨completed, afterSafe⟩ | ⟨outer, waiting, stopped⟩
  · subst childResult
    let fragment : Fragment := .node edge.entry.key.symbol fragments
    let finished := finish residual fragment after
    have fragmentBound : FragmentBound after.core.counter fragment := node_bound _ _ _ fragmentBounds
    refine ⟨r, n, p, h, k, afterCaller, finished, savedQueries, final, next, afterRoots,
      .complete fragment afterCaller savedQueries finished, ?_, post, querySame, ?_, afterPaths,
      (finish_safe residual fragment after afterSafe fragmentBound).1, afterRealized, afterCounts,
      afterFlags, fullOrigin, retained, ?_, .inl ⟨fragment, rfl,
        finish_safe residual fragment after afterSafe fragmentBound, fragmentBound⟩⟩
    · intro er en P H ek largeP largeH
      simp only [run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    · change before.core.counter ≤ after.core.counter
      omega
    · intro held inside root avoids
      have frame := protectedRoots held inside root avoids
      exact frame.trans (finish_protected residual fragment after held frame.root)
  · subst childResult
    refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
      .stopped fragments (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after),
      ?_, post, querySame, ?_, afterPaths, storage, afterRealized, afterCounts, afterFlags,
      fullOrigin, retained, protectedRoots, .inr ⟨fragments, outer, waiting, rfl⟩⟩
    · intro er en P H ek largeP largeH
      simp only [run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    · omega

end MicroCFTA.SourcePruningEnumerationSelectedEdge
