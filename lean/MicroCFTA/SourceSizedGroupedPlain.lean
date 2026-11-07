import MicroCFTA.SourceSizedGroupedIndex

/-!
# The ordinary source row shortcut

The empty annotation leaves one singleton group per original child position.
The singleton fold has the same callbacks and order as the ordinary child
fold. Reconstruction then retains the selected children in that order.

These equalities hold for arbitrary child callbacks. They preserve every
occurrence and require no language, size, sharing, or layout premise.
-/

namespace MicroCFTA.SourceSizedGroupedPlain

open Language RecursiveSize SourceSizedDecided SourceSizedGroupedChainOrder

variable {State Symbol : Type}

private theorem singleton_callbacks
    (classes : State → Nat → List (Term Symbol)) (children : List State) :
    (List.range children.length).map (fun index => groupClass classes children [index]) =
      children.map classes := by
  apply List.ext_getElem?
  intro index
  by_cases within : index < children.length
  · simp [within]
    funext size
    simp [groupClass, scaled, within]
  · simp [within]

private theorem singleton_fold
    (classes : State → Nat → List (Term Symbol)) (children : List State) :
    (((List.range children.length).map (fun index => [index])).foldl
      (fun built group => extendForests built (groupClass classes children group)) seed) =
      children.foldl (fun built child => extendForests built (classes child)) seed := by
  calc
    _ = ((List.range children.length).map
        (fun index => groupClass classes children [index])).foldl extendForests seed := by
          simp only [List.foldl_map]
    _ = (children.map classes).foldl extendForests seed := by
          rw [singleton_callbacks]
    _ = _ := by rw [List.foldl_map]

private theorem prefix_length
    (classes : State → Nat → List (Term Symbol)) (children : List State)
    (size : Nat) (selected : List (Term Symbol))
    (member : selected ∈
      (children.foldl (fun built child => extendForests built (classes child)) seed) size) :
    selected.length = children.length := by
  induction children using RecursiveSize.snoc_induction generalizing size selected with
  | empty =>
      have empty : selected = [] := by
        by_cases one : size = 1
        · simpa [seed, one] using member
        · simp [seed, one] at member
      subst selected
      rfl
  | step children last ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at member
      obtain ⟨prefixSize, _within, before, beforeIn, term, _termIn, rfl⟩ :=
        (by simpa [extendForests, List.mem_flatMap, List.mem_map] using member :
          ∃ prefixSize, prefixSize < size + 1 ∧ ∃ before,
            before ∈ (children.foldl
              (fun built child => extendForests built (classes child)) seed) prefixSize ∧
            ∃ term, term ∈ classes last (size - prefixSize) ∧ before ++ [term] = selected)
      simp only [List.length_append, List.length_cons, List.length_nil,
        ih prefixSize before beforeIn]

/-- Singleton reconstruction retains each selected child at its original position. -/
theorem assemble_singletons (symbol : Symbol) (arity : Nat) (selected : List (Term Symbol))
    (length : selected.length = arity) :
    assemble symbol arity ((List.range arity).map (fun index => [index])) selected =
      .node symbol selected := by
  subst arity
  let pairs := ((List.range selected.length).map (fun index => [index])).zip selected
  have layout : pairs.map Prod.fst = CompactGroups.childGroups selected.length [] := by
    exact List.map_fst_zip (by simp)
  have agrees : CompactEdgeRanks.SlotAgreement selected pairs := by
    intro pair present index indexIn
    obtain ⟨offset, found⟩ := List.mem_iff_getElem?.mp present
    have reads := List.getElem?_zip_eq_some.mp found
    have within : offset < selected.length := (List.getElem?_eq_some_iff.mp reads.2).1
    have expected : ((List.range selected.length).map (fun index => [index]))[offset]? =
        some [offset] := by simp [within]
    have positions : pair.1 = [offset] := Option.some.inj (reads.1.symm.trans expected)
    rw [positions] at indexIn
    have same : index = offset := List.mem_singleton.mp indexIn
    subst index
    exact reads.2
  exact Option.some.inj
    ((CompactEdgeRanks.construct_generated symbol selected.length [] pairs layout).symm.trans
      (CompactEdgeRanks.construct_original symbol selected [] pairs layout agrees))

/-- Empty constraints give exactly the ordinary paid child fold, with the same order. -/
theorem rowClass_nil_eq (classes : State → Nat → List (Term Symbol))
    (symbol : Symbol) (children : List State) (size : Nat) :
    rowClass classes symbol children [] size =
      ((children.foldl (fun built child => extendForests built (classes child)) seed) size).map
        (Term.node symbol) := by
  unfold rowClass
  simp only [CompactGroups.childGroups, List.foldl_nil]
  rw [singleton_fold]
  apply List.map_congr_left
  intro selected member
  exact assemble_singletons symbol children.length selected
    (prefix_length classes children size selected member)

/-- Both literal source branches have the same checked grouped row classes. -/
theorem sourceRowClass_eq_rowClass (classes : State → Nat → List (Term Symbol))
    (row : Row State Symbol (List (List Nat))) (size : Nat) :
    SourceSizedGroupedIndex.sourceRowClass classes row size =
      rowClass classes row.label row.children row.constraint size := by
  unfold SourceSizedGroupedIndex.sourceRowClass
  by_cases empty : row.constraint = []
  · rw [ite_eq_left empty, empty]
    exact (rowClass_nil_eq classes row.label row.children size).symm
  · exact ite_eq_right empty

/-- Every literal source row index has the checked grouped count and selector order. -/
theorem row_correct (indexes : State → RecursiveJoinFields.ValueIndex (Term Symbol))
    (classes : State → Nat → List (Term Symbol))
    (correct : ∀ state, SourceSizedGroupedIndex.Correct (indexes state) (classes state))
    (row : Row State Symbol (List (List Nat))) :
    SourceSizedGroupedIndex.Correct (SourceSizedGroupedIndex.rowIndex indexes row)
      (rowClass classes row.label row.children row.constraint) :=
  (SourceSizedGroupedIndex.row_correct indexes classes correct row).congr
    (sourceRowClass_eq_rowClass classes row)

/-- A mixed row list has exactly the checked grouped state-class order. -/
theorem state_correct (indexes : State → RecursiveJoinFields.ValueIndex (Term Symbol))
    (classes : State → Nat → List (Term Symbol))
    (correct : ∀ state, SourceSizedGroupedIndex.Correct (indexes state) (classes state))
    (rows : List (Row State Symbol (List (List Nat)))) :
    SourceSizedGroupedIndex.Correct (SourceSizedGroupedIndex.stateIndex indexes rows)
      (SourceSizedGroupedClasses.classOf classes rows) := by
  apply (SourceSizedGroupedIndex.state_correct indexes classes correct rows).congr
  intro size
  apply TablePosition.flatMap_congr
  intro row _member
  exact sourceRowClass_eq_rowClass classes row size

end MicroCFTA.SourceSizedGroupedPlain
