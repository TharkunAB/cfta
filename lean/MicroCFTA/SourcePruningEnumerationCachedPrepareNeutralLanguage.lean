import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.SourcePruningEnumerationShallowChildNeutralLanguage

/-!
# Neutral assignment language of actual cached nonterminal child rows

The original cache producer runs once and retains every receipt.
The row proof uses the same actual prepared action and returned core.
Only the older captured payload is removed from the assignment predicates.
Empty input has no accepted row.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open Language Fragments EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual cached child rows add precisely the restrictions stored by their concrete branch. -/
theorem complete_neutral_semantics
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (nonterminal : value ≠ .empty → scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) (fuel : Nat)
      (rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard)),
      SourcePruningEnumerationShallowChild.prepareChild scs value = some action ∧
      (∀ (extra : Nat), prepareChild heap (fuel + extra) scs value before = some rows) ∧
      ExceptT.run (action before.core) = rows.map (fun result => .ok (result.1, result.2.core)) ∧
      ((value = .empty ∧ rows = []) ∨
        ∃ after : EnumerationExpandableIndex.Cached Symbol EnumGuard,
          value ≠ .empty ∧ rows = [(.hole before.core.counter, after)] ∧
          after.core.counter = before.core.counter + 1 ∧
          after.core.counter = after.core.values.length ∧
          after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
          StorageValid after.core ∧ PendingRealized heap after.core ∧
          EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
          (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          FragmentBound («Symbol» := Symbol) after.core.counter (.hole before.core.counter)) ∧
      ∀ (held : Nat), held < before.core.values.length →
      ∀ (holds : NativeGuard → Term Symbol → Bool)
        (ambient : InternedGuardedLanguage.Env Symbol)
        (meaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol),
        (∃ (fragment : Fragments.Fragment Symbol)
          (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
          (fragment, after) ∈ rows ∧
          Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
            meaning assignment (EnumerationFrame.neutralize held after.core)) ↔
          Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
            meaning assignment (EnumerationFrame.neutralize held before.core) ∧
          InternedGuardedLanguage.meaning holds ambient value (assignment before.core.counter) ∧
          ∀ sc ∈ (match value with | .node _ _ _ _ => scs | _ => []),
            Suspended.Holds assignment (assignment before.core.counter) sc := by
  obtain ⟨action, fuel, rows, prepared, running, coreRaw, shape⟩ :=
    complete heap before value scs roots coherent available closed storage realized paths counts flags bounded nonterminal
  refine ⟨action, fuel, rows, prepared, running, coreRaw, shape, ?_⟩
  rcases shape with ⟨empty, rejected⟩ | ⟨after, nonempty, singleton, _rest⟩
  · intro held inside holds ambient meaning assignment
    constructor
    · rintro ⟨fragment, after, member, _satisfied⟩
      rw [rejected] at member
      cases member
    · rintro ⟨_satisfied, accepted, _suspended⟩
      simp only [empty, InternedGuardedLanguage.meaning] at accepted
  · obtain ⟨_handle, _encoded, _decoded, _rejected, _completed, semanticBranch⟩ :=
      SourcePruningEnumerationShallowChild.prepareChild_complete_neutral_semantics heap before.core scs value
        coherent available closed realized storage.aligned (nonterminal nonempty)
    obtain ⟨semanticAction, semanticAfter, semanticPrepared, semanticSuccess, semantic⟩ := semanticBranch nonempty
    have actionSame : action = semanticAction := Option.some.inj (prepared.symm.trans semanticPrepared)
    rw [← actionSame] at semanticSuccess
    have stateSame : semanticAfter = after.core := by
      simpa only [Success, coreRaw, singleton, List.map_cons, List.map_nil,
        List.mem_singleton, Except.ok.injEq, Prod.mk.injEq, true_and] using semanticSuccess
    intro held inside holds ambient meaning assignment
    constructor
    · rintro ⟨fragment, row, member, satisfied⟩
      rw [singleton] at member
      have rowSame : row = after := congrArg Prod.snd (List.mem_singleton.mp member)
      apply (semantic held inside holds ambient meaning assignment).mp
      simpa only [stateSame, rowSame] using satisfied
    · intro admitted
      refine ⟨.hole before.core.counter, after, ?_, ?_⟩
      · simp only [singleton, List.mem_singleton]
      · rw [← stateSame]
        exact (semantic held inside holds ambient meaning assignment).mpr admitted

end MicroCFTA.SourcePruningEnumerationCachedPrepare
