import MicroCFTA.SourcePruningEnumerationChildCoverage
import MicroCFTA.SourcePruningEnumerationChildCacheBounds
import MicroCFTA.SourcePruningEnumerationOrigins

/-!
# Original subtree origins through the actual child coverage witness

The original child producer runs once and retains its entire result.
Terminal cache returns do not allocate a variable.
A successful nonterminal child allocates exactly one variable and returns its hole.
The origin observer uses the same assignment extension as the old model observer.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual attached terminal child cache retains the original allocation counter. -/
theorem terminal_counter
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) (after : Cached)
    (terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true)
    (observed : (run checkEmpty r n p h k bucket incoming caller before queries).2 = some after) :
    after.core.counter = before.core.counter := by
  by_cases empty : incoming = .empty
  · simp only [run, ite_eq_left empty, Option.some.injEq] at observed
    subst after
    rfl
  · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
          have emptyFilter := congrArg Prod.fst partitioned
          simp only [List.partition_eq_filter_filter] at emptyFilter
          have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
            List.any_eq_false.mpr (List.filter_eq_nil_iff.mp emptyFilter)
          rw [terminal] at noTerminal
          cases noTerminal
      | cons first rest =>
          exact (SourcePruningEnumerationCachedTerminalAdapter.observed_cache_bounds
            checkEmpty r n p h k first rest caller before incoming descendants queries after
            (by simpa only [run, ite_eq_right empty, partitioned] using observed)).1

end MicroCFTA.SourcePruningEnumerationChildDispatch

namespace MicroCFTA.SourcePruningEnumerationChildCompletion
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationOrigins (Origin AssignmentOrigins)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the same actual model witness and every allocated original subtree path. -/
theorem complete_with_fragments_resources_accepting_origins
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
      (((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) bucket incoming beforeCaller before memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed bucket →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
        PendingFragment after.core fragment ∧
        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
          Avoids before.core.representatives held bucket →
          FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol) (term : Language.Term Symbol),
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true →
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming term →
        (∀ sc ∈ bucket, Suspended.Holds assignment term sc) →
        ∃ fragment : Fragment,
          raw = [.ok (fragment, after.core)] ∧ Fragments.fill assignment fragment = term ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol) (term : Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming term →
        (∀ sc ∈ bucket, Suspended.Holds assignment term sc) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core ∧
          raw = [.ok (fragment, after.core)] ∧ Fragments.fill extended fragment = term ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol) (term whole : Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming term →
        (∀ sc ∈ bucket, Suspended.Holds assignment term sc) →
        AssignmentOrigins whole before.core.counter assignment → Origin whole term →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragment),
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core ∧
          raw = [.ok (fragment, after.core)] ∧ Fragments.fill extended fragment = term ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core ∧
          AssignmentOrigins whole after.core.counter extended := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, retained⟩ :=
    complete_with_fragments_resources_accepting seed formulas solver inventory beforeCaller before
      checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded pending
      available closed fits reserved known
  have resources := retained.1
  rcases resources with ⟨observed, _post, _query, _growth, _paths, _storage, _realized,
    _counts, _flags, _origin, _protects, _references, _history, _shape, _fits, _known, _terminal⟩
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
    outer, waiting, retained, ?_⟩
  intro ambient residualMeaning assignment term whole original accepted holds oldOrigins termOrigin
  obtain ⟨extended, fragment, agree, originalExtended, singleton, filled, afterSatisfied⟩ :=
    retained.2 ambient residualMeaning assignment term original accepted holds
  refine ⟨extended, fragment, agree, originalExtended, singleton, filled, afterSatisfied, ?_⟩
  by_cases terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
  · have actual := observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
    simp only [Nat.add_zero] at actual
    have counter := SourcePruningEnumerationChildDispatch.terminal_counter
      checkEmpty r n p h k bucket incoming beforeCaller before memos.query after terminal
      (congrArg Prod.snd actual)
    intro uv inside
    rw [counter] at inside
    rw [agree uv inside]
    exact oldOrigins uv inside
  · have nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
      Bool.eq_false_iff.mpr terminal
    have nonempty : incoming ≠ .empty := by
      intro empty
      rw [empty, InternedGuardedLanguage.meaning] at accepted
      exact accepted
    obtain ⟨action, freshFuel, freshCache, _prepared, _raw, freshRun, grows, _rest⟩ :=
      SourcePruningEnumerationChildDispatch.nonterminal_complete checkEmpty r n p h bucket incoming
        beforeCaller before memos.query roots initial.ready.semantic.ready.semantic.1.normal.facts.coherent
        available closed nonempty safe.1 realized paths counts flags bounded nonterminal
    have canonical := freshRun k
    rw [Nat.add_comm freshFuel k] at canonical
    have actual : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (k + freshFuel)
        bucket incoming beforeCaller before memos.query =
        ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
      simpa only [Nat.add_zero] using
        observed 0 0 p h freshFuel (Nat.le_refl _) (Nat.le_refl _)
    have same : raw = [.ok (.hole before.core.counter, freshCache.core)] ∧
        afterCaller = beforeCaller ∧ savedQueries = memos.query ∧ outer = before.core ∧
        waiting = before.waiting ∧ after = freshCache := by
      simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
        actual.symm.trans canonical
    obtain ⟨rawSame, _callerSame, _querySame, _outerSame, _waitingSame, cacheSame⟩ := same
    have rowSame : (fragment, after.core) = (.hole before.core.counter, freshCache.core) :=
      Except.ok.inj ((List.cons.inj (singleton.symm.trans rawSame)).1)
    have fragmentSame : fragment = .hole before.core.counter := (Prod.mk.inj rowSame).1
    have freshTerm : extended before.core.counter = term := by
      simpa only [fragmentSame, Fragments.fill] using filled
    have counter : after.core.counter = before.core.counter + 1 := by
      simpa only [cacheSame] using grows
    intro uv inside
    by_cases old : uv < before.core.counter
    · rw [agree uv old]
      exact oldOrigins uv old
    · have fresh : uv = before.core.counter := by rw [counter] at inside; omega
      subst uv
      rw [freshTerm]
      exact termOrigin

end MicroCFTA.SourcePruningEnumerationChildCompletion
