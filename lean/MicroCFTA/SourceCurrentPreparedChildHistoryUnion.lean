import MicroCFTA.SourceCurrentNativeSlotIndex
import MicroCFTA.SourcePruningEnumerationCachedPrepare

/-! Actual prepared child rows retain input active keys at the allocated slot. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentPreparedChildHistoryUnion
open EnumerationState EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

private theorem allocation_history
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (node : Option Nat)
    (before allocated : EnumerationExpandableIndex.Cached Symbol EnumGuard) (slot : Nat)
    (observed : SourcePruningEnumerationCachedChild.allocate heap node before = some (slot, allocated)) :
    slot = before.core.counter ∧ allocated.core.expansionAncestry = before.core.expansionAncestry ∧
      allocated.core.recursionAncestry slot =
        (before.core.expansionAncestry ++ before.core.recursionAncestry slot).eraseDups := by
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated node []) with
  | none => simp [SourcePruningEnumerationCachedChild.allocate, classified] at observed
  | some flag =>
      simp only [SourcePruningEnumerationCachedChild.allocate, classified, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at observed
      rcases observed with ⟨sameSlot, sameCache⟩
      subst slot
      subst allocated
      simp [EnumerationState.allocated]

private theorem write_slot_history
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel slot : Nat) (value : UVarValue Symbol)
    (observed : SourcePruningEnumerationCachedChild.writeSlot heap fuel slot value before = some after) :
    after.core.expansionAncestry = before.core.expansionAncestry ∧
      after.core.recursionAncestry = before.core.recursionAncestry := by
  cases oldRead : before.core.values[slot]? with
  | none => simp [SourcePruningEnumerationCachedChild.writeSlot, oldRead] at observed
  | some old =>
      have written : SourcePruningEnumerationNativeIndex.write heap fuel slot value
          (references value) (references old) before = some after := by
        simpa only [SourcePruningEnumerationCachedChild.writeSlot, oldRead, Option.bind_some] using observed
      have coreSame := SourceCurrentNativeSlotIndex.write_core heap before after fuel slot value
        (references value) (references old) written
      rw [coreSame]
      exact ⟨rfl, rfl⟩

/-- Every actual prepared row retains input active keys at its counter slot. -/
theorem prepare_child_history
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel : Nat) (scs : List Suspended) (value : Value Symbol NativeGuard)
    (rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    (fragment : Fragments.Fragment Symbol)
    (observed : SourcePruningEnumerationCachedPrepare.prepareChild heap fuel scs value before = some rows)
    (member : (fragment, after) ∈ rows) :
    fragment = .hole before.core.counter ∧
      after.core.expansionAncestry = before.core.expansionAncestry ∧
      after.core.recursionAncestry before.core.counter =
        (before.core.expansionAncestry ++ before.core.recursionAncestry before.core.counter).eraseDups ∧
      ∀ key ∈ before.core.expansionAncestry, key ∈ after.core.recursionAncestry before.core.counter := by
  have exactEffects : fragment = .hole before.core.counter ∧
      after.core.expansionAncestry = before.core.expansionAncestry ∧
      after.core.recursionAncestry before.core.counter =
        (before.core.expansionAncestry ++ before.core.recursionAncestry before.core.counter).eraseDups := by
    cases value with
    | empty =>
        simp only [SourcePruningEnumerationCachedPrepare.prepareChild, Option.some.injEq] at observed
        subst rows
        simp at member
    | reference name => simp [SourcePruningEnumerationCachedPrepare.prepareChild] at observed
    | node entry edges depth free =>
        cases blocked : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
        | true => simp [SourcePruningEnumerationCachedPrepare.prepareChild,
            SourcePruningEnumerationCachedChild.prepareOrdinary, blocked] at observed
        | false =>
            cases encoded : encodeNode (.node entry edges depth free) with
            | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild,
                SourcePruningEnumerationCachedChild.prepareOrdinary, blocked, encoded] at observed
            | some handle =>
                cases allocatedRun : SourcePruningEnumerationCachedChild.allocate heap (some handle) before with
                | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild,
                    SourcePruningEnumerationCachedChild.prepareOrdinary, blocked, encoded, allocatedRun] at observed
                | some allocation =>
                    rcases allocation with ⟨slot, allocated⟩
                    cases written : SourcePruningEnumerationCachedChild.writeSlot heap fuel slot
                        (.unenumerated (some handle) scs) allocated with
                    | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild,
                        SourcePruningEnumerationCachedChild.prepareOrdinary, blocked, encoded,
                        allocatedRun, written] at observed
                    | some produced =>
                        have rowsSame : [(Fragments.Fragment.hole slot, produced)] = rows := by
                          simpa only [SourcePruningEnumerationCachedPrepare.prepareChild,
                            SourcePruningEnumerationCachedChild.prepareOrdinary, blocked, Bool.false_eq_true,
                            ite_false, encoded, Option.bind_some, allocatedRun, written, Option.map_some,
                            Option.some.injEq] using observed
                        have memberEq : (fragment, after) = (.hole slot, produced) := by
                          simpa only [← rowsSame, List.mem_singleton] using member
                        have fragmentSame : fragment = .hole slot := congrArg Prod.fst memberEq
                        have cacheSame : after = produced := congrArg Prod.snd memberEq
                        have allocationFacts := allocation_history heap (some handle) before allocated slot allocatedRun
                        have writeFacts := write_slot_history heap allocated produced fuel slot
                          (.unenumerated (some handle) scs) written
                        refine ⟨fragmentSame.trans (congrArg Fragments.Fragment.hole allocationFacts.1), ?_, ?_⟩
                        · rw [cacheSame]
                          exact writeFacts.1.trans allocationFacts.2.1
                        · rw [cacheSame, writeFacts.2, ← allocationFacts.1]
                          exact allocationFacts.2.2
    | union entry alternatives depth free =>
        cases blocked : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
        | true => simp [SourcePruningEnumerationCachedPrepare.prepareChild, blocked] at observed
        | false =>
            cases encoded : encodeNode (.union entry alternatives depth free) with
            | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild, blocked, encoded] at observed
            | some handle =>
                cases allocatedRun : SourcePruningEnumerationCachedChild.allocate heap (some handle) before with
                | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild, blocked, encoded,
                    allocatedRun] at observed
                | some allocation =>
                    rcases allocation with ⟨slot, allocated⟩
                    have rowsSame : [(Fragments.Fragment.hole slot, allocated)] = rows := by
                      simpa only [SourcePruningEnumerationCachedPrepare.prepareChild, blocked, Bool.false_eq_true,
                        ite_false, encoded, Option.bind_some, allocatedRun, Option.map_some,
                        Option.some.injEq] using observed
                    have memberEq : (fragment, after) = (.hole slot, allocated) := by
                      simpa only [← rowsSame, List.mem_singleton] using member
                    have fragmentSame : fragment = .hole slot := congrArg Prod.fst memberEq
                    have cacheSame : after = allocated := congrArg Prod.snd memberEq
                    have facts := allocation_history heap (some handle) before allocated slot allocatedRun
                    refine ⟨fragmentSame.trans (congrArg Fragments.Fragment.hole facts.1), ?_, ?_⟩
                    · rw [cacheSame]
                      exact facts.2.1
                    · rw [cacheSame, ← facts.1]
                      exact facts.2.2
    | mu entry body depth free =>
        cases blocked : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
        | true => simp [SourcePruningEnumerationCachedPrepare.prepareChild, blocked] at observed
        | false =>
            cases encoded : encodeNode (.mu entry body depth free) with
            | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild, blocked, encoded] at observed
            | some handle =>
                cases allocatedRun : SourcePruningEnumerationCachedChild.allocate heap (some handle) before with
                | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild, blocked, encoded,
                    allocatedRun] at observed
                | some allocation =>
                    rcases allocation with ⟨slot, allocated⟩
                    have rowsSame : [(Fragments.Fragment.hole slot, allocated)] = rows := by
                      simpa only [SourcePruningEnumerationCachedPrepare.prepareChild, blocked, Bool.false_eq_true,
                        ite_false, encoded, Option.bind_some, allocatedRun, Option.map_some,
                        Option.some.injEq] using observed
                    have memberEq : (fragment, after) = (.hole slot, allocated) := by
                      simpa only [← rowsSame, List.mem_singleton] using member
                    have fragmentSame : fragment = .hole slot := congrArg Prod.fst memberEq
                    have cacheSame : after = allocated := congrArg Prod.snd memberEq
                    have facts := allocation_history heap (some handle) before allocated slot allocatedRun
                    refine ⟨fragmentSame.trans (congrArg Fragments.Fragment.hole facts.1), ?_, ?_⟩
                    · rw [cacheSame]
                      exact facts.2.1
                    · rw [cacheSame, ← facts.1]
                      exact facts.2.2
  refine ⟨exactEffects.1, exactEffects.2.1, exactEffects.2.2, ?_⟩
  intro key member
  rw [exactEffects.2.2]
  simpa only [List.mem_eraseDups, List.mem_append] using
    (Or.inl member : key ∈ before.core.expansionAncestry ∨
      key ∈ before.core.recursionAncestry before.core.counter)

end MicroCFTA.SourceCurrentPreparedChildHistoryUnion
