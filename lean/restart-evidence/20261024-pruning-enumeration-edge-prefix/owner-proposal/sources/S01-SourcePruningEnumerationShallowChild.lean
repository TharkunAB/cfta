import MicroCFTA.SourcePruningEnumerationWrites

namespace MicroCFTA.SourcePruningEnumerationShallowChild
open Fragments EnumerationState EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance childMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Prepare the supported nonterminal child branches from their complete native value. -/
def prepareChild (scs : List EnumerationState.Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard) :
    Option (EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
 :=
  match value with
  | .empty => some reject
  | .reference _ => none
  | .node _ _ _ _ | .union _ _ _ _ | .mu _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
        none
      else
        match encodeNode value with
        | none => none
        | some node =>
            some (allocate (some node) >>= fun uv =>
              match value with
              | .node _ _ _ _ =>
                  setValue uv (.unenumerated (some node) scs) >>= fun _ => pure (.hole uv)
              | _ => pure (.hole uv))

/-- Derive the actual child action, fresh slot and complete realized final state. -/
theorem prepareChild_complete
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
 := by
  obtain ⟨node, encoded, decoded⟩ := available_readback heap value coherent available closed
  refine ⟨node, encoded, decoded, ?_, ?_⟩
  · intro emptyValue
    subst value
    exact ⟨rfl, by simp [Success, reject, ExceptT.run]⟩
  · intro nonempty
    obtain ⟨allocatedHandle, allocatedEncoded, allocation, allocatedSlot, allocatedRealized⟩ :=
      SourcePruningEnumerationWrites.allocate_available_realized
        heap before value coherent available closed realized aligned
    have allocatedHandleSame : allocatedHandle = node := by
      exact Option.some.inj (allocatedEncoded.symm.trans encoded)
    subst allocatedHandle
    have allocatedBound : before.counter < (allocated (some node) before).values.length := by
      exact (List.getElem?_eq_some_iff.mp allocatedSlot).elim (fun bound _ => bound)
    cases value with
    | empty => exact False.elim (nonempty rfl)
    | reference name => cases closed
    | node entry edges depth free =>
        obtain ⟨writtenHandle, after, writtenEncoded, written, afterShape, afterSlot, afterRealized⟩ :=
          SourcePruningEnumerationWrites.write_available_realized
            heap (allocated (some node) before) (.node entry edges depth free) before.counter scs
            coherent available closed allocatedRealized allocatedBound
        have writtenHandleSame : writtenHandle = node := by
          exact Option.some.inj (writtenEncoded.symm.trans encoded)
        subst writtenHandle
        refine ⟨(allocate (some node) >>= fun uv =>
          setValue uv (.unenumerated (some node) scs) >>= fun _ => pure (.hole uv)),
          after, ?_, ?_, afterShape, afterSlot, ?_, ?_, afterRealized⟩
        · simp [prepareChild, nonterminal, encoded]
        · apply (success_bind _ _ _ _ _).mpr
          refine ⟨before.counter, allocated (some node) before, allocation, ?_⟩
          apply (success_bind _ _ _ _ _).mpr
          exact ⟨(), after, written, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        · rw [afterShape]
          rfl
        · simpa only [afterShape, List.length_set] using allocated_supply (some node) before aligned
    | union entry members depth free =>
        refine ⟨(allocate (some node) >>= fun uv => pure (.hole uv)),
          allocated (some node) before, ?_, ?_, rfl, allocatedSlot, rfl,
          allocated_supply (some node) before aligned, allocatedRealized⟩
        · simp [prepareChild, nonterminal, encoded]
        · exact (success_bind _ _ _ _ _).mpr
            ⟨before.counter, allocated (some node) before, allocation,
              (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
    | mu entry body depthShape ordinaryShape =>
        refine ⟨(allocate (some node) >>= fun uv => pure (.hole uv)),
          allocated (some node) before, ?_, ?_, rfl, allocatedSlot, rfl,
          allocated_supply (some node) before aligned, allocatedRealized⟩
        · simp [prepareChild, nonterminal, encoded]
        · exact (success_bind _ _ _ _ _).mpr
            ⟨before.counter, allocated (some node) before, allocation,
              (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

end MicroCFTA.SourcePruningEnumerationShallowChild
