import MicroCFTA.SourcePruningEnumerationTerminalChildCoverage
import MicroCFTA.SourcePruningEnumerationCachedPrepareLanguage
import MicroCFTA.EnumerationConstruction

/-!
# Constructive coverage of every resource-admitted child

The terminal producer runs once and retains its full resource packet.
Terminal rows keep the original assignment. Other accepted rows install
one concrete term at the fresh variable and preserve all old constraints.
The same actual raw singleton and returned cache supply the result.
-/
namespace MicroCFTA.SourcePruningEnumerationChildCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
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

/-- An original accepted term constructs the same child singleton with only fresh assignment changes. -/
theorem complete_with_fragments_resources_accepting
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
      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
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
              ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core := by
  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting,
    observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, protects, references, history, shape, returnedFits, returnedKnown, terminalAccepting⟩ :=
    complete_with_fragments_resources_terminal_accepting seed formulas solver inventory beforeCaller before
      checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded pending
      available closed fits reserved known
  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting,
    ⟨observed, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
      origin, protects, references, history, shape, returnedFits, returnedKnown, terminalAccepting⟩, ?_⟩
  intro ambient residualMeaning assignment term beforeSatisfied accepted holds
  by_cases terminalAny : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
  · obtain ⟨fragment, singleton, filled, afterSatisfied⟩ :=
      terminalAccepting ambient residualMeaning assignment term terminalAny beforeSatisfied accepted holds
    exact ⟨assignment, fragment, fun _ _ => rfl, beforeSatisfied, singleton, filled, afterSatisfied⟩
  · have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
      Bool.eq_false_iff.mpr terminalAny
    have incomingNonempty : incoming ≠ .empty := by
      intro empty
      rw [empty, InternedGuardedLanguage.meaning] at accepted
      exact accepted
    let extended := EnumerationCorrectness.install assignment before.core.counter [term]
    have agree : ∀ uv < before.core.counter, extended uv = assignment uv :=
      EnumerationCorrectness.install_before assignment before.core.counter [term]
    have fresh : extended before.core.counter = term := by
      simp only [extended, EnumerationCorrectness.install, ↓reduceIte]
    have originalExtended : Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core :=
      (EnumerationCorrectness.state_assignment_congr _ _ before.core safe.1 extended assignment agree).mpr
        beforeSatisfied
    have extendedHolds : ∀ sc ∈ bucket, Suspended.Holds extended term sc := by
      intro sc member
      exact EnumerationConstruction.holds_extension assignment extended before.core.counter agree sc
        (bounded sc member) term (holds sc member)
    have effectiveHolds : ∀ sc ∈ (match incoming with | .node _ _ _ _ => bucket | _ => []),
        Suspended.Holds extended term sc := by
      cases incoming with
      | node _ _ _ _ => exact extendedHolds
      | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
          intro sc member
          cases member
    have noHere : (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
      simp only [List.partition_eq_filter_filter]
      exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp noTerminal sc member)
    cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      have hereSame : here = [] := by simpa only [partitioned] using noHere
      subst here
      obtain ⟨action, indexFuel, rows, prepared, cachedRun, rawRun, cachedShape, rowMeaning⟩ :=
        SourcePruningEnumerationCachedPrepare.complete_semantics beforeCaller.checked.native.machine.heap
          before incoming bucket roots initial.ready.semantic.ready.semantic.1.normal.facts.coherent
          available closed safe.1 realized paths counts flags bounded (fun _ => noTerminal)
      rcases cachedShape with ⟨emptyValue, _emptyRows⟩ | ⟨nextCache, _nonempty, rowsSame, _rest⟩
      · exact (incomingNonempty emptyValue).elim
      · have cachedAt := cachedRun k
        rw [Nat.add_comm indexFuel k] at cachedAt
        have canonicalObserved :
            SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (k + indexFuel)
              bucket incoming beforeCaller before memos.query =
              ((.ok (some [.ok (.hole before.core.counter, nextCache.core)]),
                beforeCaller, memos.query, before.core, before.waiting), some nextCache) := by
          simp only [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
            ite_eq_right incomingNonempty, partitioned, prepared, cachedAt, rowsSame, rawRun,
            List.map_cons, List.map_nil]
        have actualObserved :
            SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (k + indexFuel)
              bucket incoming beforeCaller before memos.query =
              ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
          simpa only [Nat.add_zero] using
            observed 0 0 p h indexFuel (Nat.le_refl _) (Nat.le_refl _)
        have same : raw = [.ok (.hole before.core.counter, nextCache.core)] ∧
            afterCaller = beforeCaller ∧ savedQueries = memos.query ∧
            outer = before.core ∧ waiting = before.waiting ∧ after = nextCache := by
          simpa only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq, and_assoc] using
            actualObserved.symm.trans canonicalObserved
        obtain ⟨rawSame, callerSame, _queriesSame, _outerSame, _waitingSame, cacheSame⟩ := same
        obtain ⟨rowFragment, rowCache, member, rowSatisfied⟩ :=
          (rowMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient residualMeaning extended).mpr
            ⟨originalExtended, by simpa only [fresh] using accepted,
              fun sc member => by
                cases incoming <;> simpa only [fresh] using effectiveHolds sc member⟩
        have rowSame : (rowFragment, rowCache) = (.hole before.core.counter, nextCache) :=
          List.mem_singleton.mp (by simpa only [rowsSame] using member)
        have rowCacheSame : rowCache = nextCache := congrArg Prod.snd rowSame
        refine ⟨extended, .hole before.core.counter, agree, originalExtended, ?_, ?_, ?_⟩
        · simpa only [cacheSame] using rawSame
        · simpa only [Fragments.fill] using fresh
        · simpa only [callerSame, cacheSame, rowCacheSame] using rowSatisfied

end MicroCFTA.SourcePruningEnumerationChildCompletion
