import MicroCFTA.SourcePruningEnumerationShallowChild
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningEnumerationPendingWriteLanguage

/-!
# Assignment language of actual fresh child slots

An ordinary child stores its full suspended constraints in the fresh slot.
Union and Mu child slots store only their native node domain. Their source
branches truncate recursion. They do not retain the incoming bucket.
The original child producer runs once and retains every original receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationShallowChild
open Language Fragments EnumerationState EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- A fresh slot with a stored bucket adds exactly its node domain and suspended constraints. -/
theorem allocation_bucket_semantics
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : EnumerationState.State Symbol EnumGuard)
    (handle : Nat) (scs : List EnumerationState.Suspended)
    (aligned : before.counter = before.values.length) :
    Satisfies language meaning assignment
      {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} ↔
      Satisfies language meaning assignment before ∧ language handle (assignment before.counter) ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment before.counter) sc := by
  have written := SourcePruningEnumerationPendingWriteLanguage.pending_write
    language meaning assignment (allocated (some handle) before)
    {allocated (some handle) before with values :=
      (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)}
    before.counter handle (some handle) [] scs (fun _ => True)
    (allocated_slot (some handle) before aligned) rfl (by simp only [List.append_nil]) rfl
    (by intro term; simp [permits])
  rw [written, allocation_semantics language meaning assignment (some handle) before aligned]
  simp only [Option.map_some, permits, true_and, and_assoc]

/-- The actual child producer retains its receipts and the exact branch-specific assignment restrictions. -/
theorem prepareChild_complete_semantics
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard)
    (scs : List EnumerationState.Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (realized : PendingRealized heap before) (aligned : before.counter = before.values.length)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ node : Nat, encodeNode value = some node ∧ lookupNode heap node = some value ∧
      (value = .empty →
        prepareChild scs value = some (reject : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) ∧
        ¬ ∃ (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol EnumGuard),
          Success (reject : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) before fragment after) ∧
      (value ≠ .empty →
        ∃ (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
          (after : EnumerationState.State Symbol EnumGuard),
          prepareChild scs value = some action ∧ Success action before (.hole before.counter) after ∧
          after = (match value with
            | .node _ _ _ _ =>
                {allocated (some node) before with values :=
                  (allocated (some node) before).values.set before.counter (.unenumerated (some node) scs)}
            | _ => allocated (some node) before) ∧
          after.values[before.counter]? = some (.unenumerated (some node)
            (match value with | .node _ _ _ _ => scs | _ => [])) ∧
          after.counter = before.counter + 1 ∧ after.counter = after.values.length ∧
          PendingRealized heap after)
 ∧
      (value ≠ .empty →
        ∃ (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
          (after : EnumerationState.State Symbol EnumGuard),
          prepareChild scs value = some action ∧ Success action before (.hole before.counter) after ∧
          ∀ (holds : NativeGuard → Term Symbol → Bool)
            (ambient : InternedGuardedLanguage.Env Symbol)
            (meaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol),
            Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
              meaning assignment after ↔
              Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
                meaning assignment before ∧
              InternedGuardedLanguage.meaning holds ambient value (assignment before.counter) ∧
              ∀ sc ∈ (match value with | .node _ _ _ _ => scs | _ => []),
                Suspended.Holds assignment (assignment before.counter) sc) := by
  obtain ⟨node, encoded, decoded, rejected, completed⟩ :=
    prepareChild_complete heap before scs value coherent available closed realized aligned nonterminal
  refine ⟨node, encoded, decoded, rejected, completed, ?_⟩
  intro nonempty
  obtain ⟨action, after, prepared, success, afterSame, _stored, _counter, _aligned, _realized⟩ :=
    completed nonempty
  refine ⟨action, after, prepared, success, ?_⟩
  intro holds ambient meaning assignment
  have decodedMeaning := SourcePruningEnumerationNativeLanguage.handles_lookup
    holds ambient heap node value (assignment before.counter) decoded
  rw [afterSame]
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => cases closed
  | node entry edges depth free =>
      simpa only [decodedMeaning] using
        allocation_bucket_semantics (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
          meaning assignment before node scs aligned
  | union entry members depth free | mu entry body depth free =>
      simpa only [decodedMeaning, Option.map_some, permits, List.not_mem_nil, false_implies,
        implies_true, and_true] using
        allocation_semantics (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
          meaning assignment (some node) before aligned

end MicroCFTA.SourcePruningEnumerationShallowChild
