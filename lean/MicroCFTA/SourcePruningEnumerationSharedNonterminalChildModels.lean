import MicroCFTA.SourcePruningEnumerationSharedChildCompletion
import MicroCFTA.SourcePruningEnumerationShallowChildLanguage
import MicroCFTA.SourcePruningEnumerationOrigins

/-!
# Original assignments for actual shared nonterminal children

One compatible child term supplies the fresh slot's assignment and origin.
The actual shared operation supplies the returned cache and its indexes.
An ordinary child stores its bucket. An opaque child can store an empty bucket.
This forward construction does not restore dropped constraints backward.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationOrigins
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A compatible original term extends one actual nonterminal child's model and origins. -/
theorem nonterminal_models_origins
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : Cached) (queries : Queries) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent beforeCaller.checked.native.machine.heap)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = [])
    (storage : StorageValid before.core)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (whole term : Term Symbol)
    (satisfied : Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      beforeCaller.checked.native.machine.heap) meaning assignment before.core)
    (accepted : InternedGuardedLanguage.meaning holds ambient incoming term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc)
    (old : AssignmentOrigins whole before.core.counter assignment)
    (origin : Origin whole term) :
    ∃ (action : EnumerateM Symbol Constraint (Fragment Symbol)) (fuel : Nat)
      (after : Cached) (extended : Nat → Term Symbol),
      SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action ∧
      ExceptT.run (action before.core) = [.ok (.hole before.core.counter, after.core)] ∧
      (∀ extra, run checkEmpty representativeFuel nativeFuel p h (fuel + extra)
        scs incoming beforeCaller before queries =
        ((.ok (some [.ok (.hole before.core.counter, after.core)]),
          beforeCaller, queries, before.core, before.waiting), some after)) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧
      Roots after.core.representatives roots ∧
      StorageValid after.core ∧
      PendingRealized beforeCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate
        beforeCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      FragmentBound after.core.counter (.hole before.core.counter : Fragment Symbol) ∧
      extended = install assignment before.core.counter [term] ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
        beforeCaller.checked.native.machine.heap) meaning extended before.core ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
        beforeCaller.checked.native.machine.heap) meaning extended after.core ∧
      (∀ sc ∈ scs, Suspended.Holds extended term sc) ∧
      Fragments.fill extended (.hole before.core.counter) = term ∧
      AssignmentOrigins whole after.core.counter extended := by
  have nonempty : incoming ≠ .empty := by
    intro same
    subst incoming
    simp only [InternedGuardedLanguage.meaning] at accepted
  obtain ⟨action, fuel, after, prepared, actionRun, observed, counter, aligned, forestSame,
    afterPaths, afterStorage, afterRealized, afterCounts, afterFlags, fragmentBound⟩ :=
    nonterminal_complete checkEmpty representativeFuel nativeFuel p h scs incoming
      beforeCaller before queries roots coherent available closed nonempty storage realized
      paths counts flags bounded nonterminal
  let extended := install assignment before.core.counter [term]
  have agree : ∀ uv < before.core.counter, extended uv = assignment uv := by
    intro uv inside
    exact install_before assignment before.core.counter [term] uv inside
  have fresh : extended before.core.counter = term := by
    simp only [extended, install, ↓reduceIte]
  have beforeModel : Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      beforeCaller.checked.native.machine.heap) meaning extended before.core :=
    (state_assignment_congr _ meaning before.core storage extended assignment agree).mpr satisfied
  have extendedHeld : ∀ sc ∈ scs, Suspended.Holds extended term sc := by
    intro sc member path represented
    rw [agree sc.var (bounded sc member)]
    exact inherited sc member path represented
  obtain ⟨_handle, _encoded, _decoded, _rejected, _produced, models⟩ :=
    SourcePruningEnumerationShallowChild.prepareChild_complete_semantics
      beforeCaller.checked.native.machine.heap before.core scs incoming coherent available closed
      realized storage.aligned nonterminal
  obtain ⟨semanticAction, semanticAfter, semanticPrepared, semanticSuccess, exactModels⟩ :=
    models nonempty
  have actionSame : semanticAction = action :=
    Option.some.inj (semanticPrepared.symm.trans prepared)
  subst semanticAction
  change (.ok (.hole before.core.counter, semanticAfter)) ∈
    ExceptT.run (action before.core) at semanticSuccess
  rw [actionRun] at semanticSuccess
  have coreSame : semanticAfter = after.core :=
    congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp semanticSuccess))
  rw [coreSame] at exactModels
  have afterModel : Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      beforeCaller.checked.native.machine.heap) meaning extended after.core := by
    apply (exactModels holds ambient meaning extended).mpr
    refine ⟨beforeModel, ?_, ?_⟩
    · simpa only [fresh] using accepted
    · cases incoming with
      | node _ _ _ _ =>
        intro sc member
        rw [fresh]
        exact extendedHeld sc member
      | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
        intro sc member
        cases member
  refine ⟨action, fuel, after, extended, prepared, actionRun, observed, counter, aligned,
    forestSame, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags, fragmentBound,
    rfl, agree, beforeModel, afterModel, extendedHeld, ?_, ?_⟩
  · simpa only [Fragments.fill] using fresh
  · rw [counter]
    simpa using install_origins assignment before.core.counter [term] whole old
      (fun child member => by
        have same : child = term := List.mem_singleton.mp member
        simpa only [same] using origin)

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
