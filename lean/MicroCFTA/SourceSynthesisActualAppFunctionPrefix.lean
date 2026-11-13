import MicroCFTA.SourceCurrentRequiredQueryMemos

namespace MicroCFTA.SourceSynthesisActualAppFunctionPrefix
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredGraph SourceCurrentRequiredQueryMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

private theorem children_split_at
    [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {memos saved : EndpointMemoGateTrace.Memos}
    (trace : RequireChildren entries index values before results after)
    (reads : ChildrenReads trace memos saved) (bounded : count ≤ values.length) :
    ∃ prefixResults suffixResults middle middleMemos,
      results = prefixResults ++ suffixResults ∧
      (∃ earlier : RequireChildren entries index (values.take count) before prefixResults middle,
        ChildrenReads earlier memos middleMemos) ∧
      (∃ later : RequireChildren entries (index + count) (values.drop count) middle suffixResults after,
        ChildrenReads later middleMemos saved) := by
  cases count with
  | zero =>
      exact ⟨[], results, before, memos, rfl, ⟨.nil, .nil⟩,
        by simpa only [List.drop_zero, Nat.add_zero] using ⟨trace, reads⟩⟩
  | succ count =>
      cases values with
      | nil => simp at bounded
      | cons value values =>
          cases reads with
          | unselected rest =>
              have absent : SourceEqualityNeededMap.lookup (index : Int) entries = none := by
                assumption
              obtain ⟨prefixResults, suffixResults, middle, middleMemos,
                  aligned, ⟨earlier, earlierReads⟩, later⟩ :=
                children_split_at count _ rest (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using bounded)
              refine ⟨value :: prefixResults, suffixResults, middle, middleMemos,
                ?_, ⟨.unselected index absent earlier, .unselected (absent := absent) earlierReads⟩, ?_⟩
              · exact congrArg (List.cons value) aligned
              · simpa only [List.drop_succ_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later
          | selected first rest =>
              rename_i needed tailResults headResult afterFirst firstMemos found firstTrace restTrace
              obtain ⟨prefixResults, suffixResults, middle, middleMemos,
                  aligned, ⟨earlier, earlierReads⟩, later⟩ :=
                children_split_at count _ rest (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using bounded)
              refine ⟨headResult :: prefixResults, suffixResults, middle, middleMemos,
                ?_, ⟨.selected index found firstTrace earlier, .selected (found := found) first earlierReads⟩, ?_⟩
              · exact congrArg (List.cons headResult) aligned
              · simpa only [List.drop_succ_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later
termination_by count

/-- The same completed app reads derive the function read and its initial heap invariants. -/
theorem actual_app_function_read_prefix
    [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List (List Int)) (entries : List (Int × SourceEqualityNeeded.Needed))
    (wanted : SourceEqualityNeeded.Needed)
    (compiled : SourceEqualityNeeded.build paths = .node entries)
    (selected : SourceEqualityNeededMap.lookup 2 entries = some wanted)
    (resultType marker function argument : Value Symbol Guard)
    (results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (memos saved : EndpointMemoGateTrace.Memos)
    (reads : RequireAllReads paths [resultType, marker, function, argument]
      results before after memos saved)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before [resultType, marker, function, argument]) :
    ∃ prefixResults functionResult suffixResults functionBefore functionAfter
        functionMemos returnedMemos,
      results = prefixResults ++ functionResult :: suffixResults ∧
      prefixResults.length = 2 ∧
      (∃ earlier : RequireChildren entries 0 [resultType, marker]
          before prefixResults functionBefore,
        ChildrenReads earlier memos functionMemos) ∧
      (∃ actual : RequireNode wanted function functionBefore functionResult functionAfter,
        NodeReads actual functionMemos returnedMemos) ∧
      (∃ later : RequireChildren entries 3 [argument]
          functionAfter suffixResults after,
        ChildrenReads later returnedMemos saved) ∧
      SourceEqualityRequiredCache.Keeps before functionBefore ∧
      SourceEqualityRequiredSemanticCache.SemanticReady functionBefore ∧
      InternedFreshOrdinaryCostHeap.Heap functionBefore ∧
      Available functionBefore function := by
  simp only [RequireAllReads, compiled] at reads
  obtain ⟨trace, reads⟩ := reads
  obtain ⟨prefixResults, suffixResults, middle, middleMemos,
      aligned, ⟨earlier, earlierReads⟩, ⟨later, laterReads⟩⟩ :=
    children_split_at 2 trace reads (by simp)
  have prefixAvailable : Values before [resultType, marker] := by
    intro value member
    apply available value
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True)
    earlier semantic costs (by intro _ _ _; trivial) prefixAvailable
  have retained : Available middle function :=
    effects.1.available function (available function (by simp))
  cases laterReads with
  | unselected _rest =>
      have absent : SourceEqualityNeededMap.lookup 2 entries = none := by assumption
      rw [selected] at absent
      cases absent
  | selected actual rest =>
      rename_i actualNeeded tailResults functionResult functionAfter returnedMemos found actualTrace restTrace
      have same : wanted = actualNeeded := Option.some.inj (selected.symm.trans found)
      cases same
      exact ⟨prefixResults, functionResult, tailResults, middle, functionAfter,
        middleMemos, returnedMemos, aligned, earlier.length, ⟨earlier, earlierReads⟩,
        ⟨actualTrace, actual⟩, ⟨restTrace, rest⟩, effects.1, effects.2.1,
        effects.2.2.1, retained⟩

/-- An absent function request retains the function between the same prefix and suffix. -/
theorem actual_app_function_unselected_prefix
    [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List (List Int)) (entries : List (Int × SourceEqualityNeeded.Needed))
    (compiled : SourceEqualityNeeded.build paths = .node entries)
    (unselected : SourceEqualityNeededMap.lookup 2 entries = none)
    (resultType marker function argument : Value Symbol Guard)
    (results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (memos saved : EndpointMemoGateTrace.Memos)
    (reads : RequireAllReads paths [resultType, marker, function, argument]
      results before after memos saved)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before [resultType, marker, function, argument]) :
    ∃ prefixResults suffixResults functionBefore functionMemos,
      results = prefixResults ++ function :: suffixResults ∧
      prefixResults.length = 2 ∧
      (∃ earlier : RequireChildren entries 0 [resultType, marker]
          before prefixResults functionBefore,
        ChildrenReads earlier memos functionMemos) ∧
      (∃ later : RequireChildren entries 3 [argument]
          functionBefore suffixResults after,
        ChildrenReads later functionMemos saved) ∧
      SourceEqualityRequiredCache.Keeps before functionBefore ∧
      SourceEqualityRequiredSemanticCache.SemanticReady functionBefore ∧
      InternedFreshOrdinaryCostHeap.Heap functionBefore ∧
      Available functionBefore function := by
  simp only [RequireAllReads, compiled] at reads
  obtain ⟨trace, reads⟩ := reads
  obtain ⟨prefixResults, suffixResults, middle, middleMemos,
      aligned, ⟨earlier, earlierReads⟩, ⟨later, laterReads⟩⟩ :=
    children_split_at 2 trace reads (by simp)
  have prefixAvailable : Values before [resultType, marker] := by
    intro value member
    apply available value
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True)
    earlier semantic costs (by intro _ _ _; trivial) prefixAvailable
  have retained : Available middle function :=
    effects.1.available function (available function (by simp))
  cases laterReads with
  | unselected rest =>
      exact ⟨prefixResults, _, middle, middleMemos, aligned, earlier.length,
        ⟨earlier, earlierReads⟩, ⟨_, rest⟩, effects.1, effects.2.1,
        effects.2.2.1, retained⟩
  | selected _actual _rest =>
      have found : ∃ wanted, SourceEqualityNeededMap.lookup 2 entries = some wanted :=
        ⟨_, by assumption⟩
      obtain ⟨wanted, found⟩ := found
      rw [unselected] at found
      cases found

end MicroCFTA.SourceSynthesisActualAppFunctionPrefix
