import MicroCFTA.SourcePruningEnumerationParkedLanguage

namespace MicroCFTA.SourcePruningEnumerationRecursion
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompressionFrame SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] recursionMonadList

private theorem true_check_write
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : State Symbol EnumGuard) (fuel uv handle : Nat) (scs : List Suspended)
    (ready : EnumerationDriver.Ready uv before)
    (observed : Success (checkRepeated heap fuel uv handle scs) before true after) :
    ∃ resolved, Frame before resolved ∧
      Success (setValue uv (.unenumerated (some handle) [])) resolved () after := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        obtain ⟨same, _safe, _counter, _protected⟩ := EnumerationDriver.representative_root fuel uv root
          before resolved ready.safe ready.inside ready.root resolution
        subst root
        have frame := representative_frame fuel uv uv before resolved ready.safe.1.total resolution
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current currentState
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
        · simp only [seen, ↓reduceIte] at continued
          obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_same, afterSame⟩ := (success_pure true true cleared after).mp returned
          subst after
          exact ⟨resolved, frame, written⟩
        · have impossible : Success (pure false) resolved true after := by
            simpa only [seen, ↓reduceIte] using continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
          cases impossible
      · have impossible : Success (pure false) before true after := by
          simpa only [checkRepeated, decoded, boundary, Bool.false_eq_true, ↓reduceIte] using observed
        obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
        cases impossible

/-- An actual selected clear retains every bucket in a closed dependency set. -/
theorem selected_clear_keeps_closed_references
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv)
    (fuel handle : Nat) (scs : List Suspended) (after : State Symbol EnumGuard)
    (observed : Success (checkRepeated heap fuel uv handle scs) before.core true after)
    (vertices : List Nat)
    (cycle : ∀ target ∈ vertices, ∃ source ∈ vertices,
      ∃ value, before.core.values[source]? = some value ∧
        ∃ sc ∈ references value, UnionFind.SameClass before.core.representatives target sc.var) :
    (∀ vertex ∈ vertices, after.values[vertex]? = before.core.values[vertex]?) ∧
    (∀ left right, UnionFind.SameClass after.representatives left right ↔
      UnionFind.SameClass before.core.representatives left right) ∧
    (∀ (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) vertex, vertex ∈ vertices →
      (slotSatisfies assignment vertex (EnumerationCorrectness.heap language after.values vertex) ↔
        slotSatisfies assignment vertex (EnumerationCorrectness.heap language before.core.values vertex))) := by
  have ready := SourcePruningEnumerationSelection.ready heap before preference uv safe roots paths counts flags selected
  have incoming := SourcePruningEnumerationSelection.incoming heap before preference uv safe roots paths counts flags selected
  have separate : ∀ vertex ∈ vertices, vertex ≠ uv := by
    intro vertex member same
    subst vertex
    obtain ⟨source, _sourceMember, value, stored, sc, listed, alias⟩ := cycle uv member
    exact incoming value (List.mem_iff_getElem?.mpr ⟨source, stored⟩) sc listed alias
  obtain ⟨resolved, frame, written⟩ := true_check_write heap before.core after fuel uv handle scs ready observed
  have shape := (EnumerationDriver.modify_success _ resolved after).mp written
  have kept : ∀ vertex ∈ vertices, after.values[vertex]? = before.core.values[vertex]? := by
    intro vertex member
    simp only [shape, frame.values]
    simp [Ne.symm (separate vertex member)]
  refine ⟨kept, ?_, ?_⟩
  · intro left right
    change UnionFind.SameClass after.representatives left right ↔ _
    rw [shape]
    constructor
    · rintro ⟨root, size, first, second⟩
      exact ⟨root, size, (frame.reaches left root size).mp first, (frame.reaches right root size).mp second⟩
    · rintro ⟨root, size, first, second⟩
      exact ⟨root, size, (frame.reaches left root size).mpr first, (frame.reaches right root size).mpr second⟩
  · intro language assignment vertex member
    simp only [EnumerationCorrectness.heap, kept vertex member]

/-- Proper suspended paths cannot form a finite closed cycle in one assignment. -/
theorem proper_closed_references_no_assignment
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (state : State Symbol EnumGuard) (vertices : List Nat) (nonempty : vertices ≠ [])
    (cycle : ∀ target ∈ vertices, ∃ source ∈ vertices, ∃ node scs,
      state.values[source]? = some (.unenumerated node scs) ∧
      ∃ sc ∈ scs, ∃ path ∈ EqualityTrie.fromPathTrie sc.trie,
        path ≠ [] ∧ UnionFind.SameClass state.representatives target sc.var) :
    ¬ ∃ assignment, Satisfies language meaning assignment state := by
  rintro ⟨assignment, satisfied⟩
  have step : ∀ target ∈ vertices, ∃ source ∈ vertices,
      (assignment target).height < (assignment source).height := by
    intro target member
    obtain ⟨source, sourceMember, node, scs, stored, sc, listed, path, pathMember, proper, alias⟩ := cycle target member
    have bucket : permits (node.map language) (assignment source) ∧
        ∀ suspended ∈ scs, Suspended.Holds assignment (assignment source) suspended := by
      simpa only [EnumerationCorrectness.heap, stored, Option.getD_some, slot, slotSatisfies,
        List.forall_mem_map] using satisfied.1.2 source
    have reaches := bucket.2 sc listed path pathMember
    have equal := satisfied.1.1 target sc.var alias
    have located : (assignment source).atPath path = some (assignment target) := by
      simpa only [← equal] using reaches
    have bound := atPath_height_bound _ _ _ located
    have positive : 0 < path.length := by
      cases path with
      | nil => exact False.elim (proper rfl)
      | cons => exact Nat.zero_lt_succ _
    exact ⟨source, sourceMember, by omega⟩
  have bounded : ∀ (xs : List Nat) vertex, vertex ∈ xs →
      (assignment vertex).height ≤ xs.foldr (fun index bound => max (assignment index).height bound) 0 := by
    intro xs
    induction xs with
    | nil => intro vertex member; cases member
    | cons first rest ih =>
        intro vertex member
        rcases List.mem_cons.mp member with same | later
        · subst vertex
          exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih vertex later) (Nat.le_max_right _ _)
  have initial : ∃ vertex, vertex ∈ vertices := by
    cases vertices with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest => exact ⟨first, by simp⟩
  have tall : ∀ bound, ∃ vertex ∈ vertices, bound ≤ (assignment vertex).height := by
    intro bound
    induction bound with
    | zero => obtain ⟨vertex, member⟩ := initial; exact ⟨vertex, member, Nat.zero_le _⟩
    | succ bound ih =>
        obtain ⟨vertex, member, height⟩ := ih
        obtain ⟨source, sourceMember, larger⟩ := step vertex member
        exact ⟨source, sourceMember, by omega⟩
  obtain ⟨vertex, member, tooHigh⟩ := tall (vertices.foldr (fun index bound => max (assignment index).height bound) 0 + 1)
  have tooLow := bounded vertices vertex member
  omega

/-- An actual selected clear cannot remove a proper suspended-cycle obstruction. -/
theorem selected_clear_proper_cycle_unsatisfiable
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv)
    (fuel handle : Nat) (scs : List Suspended) (after : State Symbol EnumGuard)
    (observed : Success (checkRepeated heap fuel uv handle scs) before.core true after)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (vertices : List Nat) (nonempty : vertices ≠ [])
    (cycle : ∀ target ∈ vertices, ∃ source ∈ vertices, ∃ node bucket,
      before.core.values[source]? = some (.unenumerated node bucket) ∧
      ∃ sc ∈ bucket, ∃ path ∈ EqualityTrie.fromPathTrie sc.trie,
        path ≠ [] ∧ UnionFind.SameClass before.core.representatives target sc.var) :
    ¬ ∃ assignment, Satisfies language meaning assignment after := by
  have referenceCycle : ∀ target ∈ vertices, ∃ source ∈ vertices,
      ∃ value, before.core.values[source]? = some value ∧
        ∃ sc ∈ references value, UnionFind.SameClass before.core.representatives target sc.var := by
    intro target member
    obtain ⟨source, sourceMember, node, bucket, stored, sc, listed, _path, _pathMember, _proper, alias⟩ := cycle target member
    exact ⟨source, sourceMember, .unenumerated node bucket, stored, sc, listed, alias⟩
  have kept := selected_clear_keeps_closed_references heap before preference uv roots safe paths counts flags selected
    fuel handle scs after observed vertices referenceCycle
  apply proper_closed_references_no_assignment language meaning after vertices nonempty
  intro target member
  obtain ⟨source, sourceMember, node, bucket, stored, sc, listed, path, pathMember, proper, alias⟩ := cycle target member
  exact ⟨source, sourceMember, node, bucket, (kept.1 source sourceMember).trans stored,
    sc, listed, path, pathMember, proper, (kept.2.1 target sc.var).mpr alias⟩

end MicroCFTA.SourcePruningEnumerationRecursion
