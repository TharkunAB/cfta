import MicroCFTA.SourceEntailment

/-!
# Actual representatives preserve complete subtree identity

The sparse actual table can retain more identity classes than the complete
table. It cannot combine distinct complete subtrees. These proofs use the
executed representative search, including its named-leaf and fallback cases.
-/
namespace MicroCFTA.ActualQuotient
open SourceGuards SourceObservations

private theorem filterMap_congr (entries : List α) (left right : α → Option β)
    (same : ∀ entry ∈ entries, left entry = right entry) : entries.filterMap left = entries.filterMap right := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.filterMap_cons, same entry (by simp), ih (fun value member => same value (by simp [member]))]

/-- Empty structural scopes preserve every complete constructor tree. -/
theorem renameTree_empty (formulas : Formulas Formula) (term : Language.Term (Label Formula)) :
    renameTree formulas [] term = term := by
  cases term with
  | node label children =>
      simp only [renameTree, renameRoot, List.foldl_nil]
      congr 1
      calc
        List.map (renameTree formulas []) children = children.map (fun child => child) := by
          apply List.map_congr_left
          intro child _
          exact renameTree_empty formulas child
        _ = children := List.map_id' children
termination_by sizeOf term

/-- Complete equality with empty scopes identifies exactly one existing subtree. -/
theorem sameTerm_empty_true [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (left right : Path) :
    sameTerm formulas term [] left right = some true ↔
      ∃ subtree, Language.Term.atPath term left = some subtree ∧ Language.Term.atPath term right = some subtree := by
  cases first : Language.Term.atPath term left with
  | none => simp [sameTerm, first]
  | some a =>
      cases second : Language.Term.atPath term right with
      | none => simp [sameTerm, first, second]
      | some b =>
          simp only [sameTerm, first, second, Bind.bind, Option.bind, Pure.pure, renameTree_empty, Option.some.injEq]
          change Language.termEq a b = true ↔ ∃ subtree, a = subtree ∧ b = subtree
          constructor
          · intro same
            exact ⟨b, (Language.termEq_correct a b).mp same, rfl⟩
          · rintro ⟨subtree, rfl, rfl⟩
            exact (Language.termEq_correct _ _).mpr rfl

/-- Every actual-table entry comes from its stated observed name and refinement. -/
theorem actual_observed (observed : Observations Formula) (guard : Guard Formula)
    (actual : Actual Formula) (member : actual ∈ actuals observed guard) :
    ∃ value, observed actual.target = some value ∧ value.name = actual.name ∧ value.refinement = actual.refinement := by
  obtain ⟨target, _, found⟩ := List.mem_filterMap.mp member
  cases observation : observed target with
  | none => simp [observation] at found
  | some value =>
      simp only [observation, Option.map_some, Option.some.injEq] at found
      subst actual
      exact ⟨value, observation, rfl, rfl⟩

/-- Equal named and refined leaves are equal complete trees. -/
theorem observed_leaves_same [DecidableEq Formula] (term : Language.Term (Label Formula))
    (left right : Path) (first second : Observed Formula)
    (hl : observe term left = some first) (hr : observe term right = some second)
    (names : first.name = second.name) (annotations : first.refinement = second.refinement)
    (leafLeft : first.leafness = .leaf) (leafRight : second.leafness = .leaf) :
    Language.Term.atPath term left = Language.Term.atPath term right := by
  cases a : Language.Term.atPath term left with
  | none => simp [observe, a] at hl
  | some l =>
      cases b : Language.Term.atPath term right with
      | none => simp [observe, b] at hr
      | some r =>
          have leftRoot : rootObservation l = first := by simpa [observe, a] using hl
          have rightRoot : rootObservation r = second := by simpa [observe, b] using hr
          have same : compareObserved (rootObservation l) (rootObservation r) = some true := by
            simp [leftRoot, rightRoot, compareObserved, names, annotations, leafLeft, leafRight]
          have equal := (Language.termEq_correct l r).mp (compareObserved_sound l r true same)
          simp [equal]

/-- Every returned representative denotes the same complete subtree as its actual. -/
theorem representative_same [DecidableEq Formula] (term : Language.Term (Label Formula))
    (sameAt : Path → Path → Option Bool)
    (sound : ∀ left right, sameAt left right = some true →
      Language.Term.atPath term left = Language.Term.atPath term right)
    (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard) :
    Language.Term.atPath term (representative (observe term) sameAt (actuals (observe term) guard) actual) =
      Language.Term.atPath term actual.target := by
  unfold representative
  split
  · rename_i canonical selected
    have accepted := List.find?_some selected
    have otherMember := List.mem_of_find?_eq_some selected
    obtain ⟨first, firstAt, firstName, firstRefinement⟩ := actual_observed (observe term) guard actual member
    obtain ⟨second, secondAt, secondName, secondRefinement⟩ := actual_observed (observe term) guard canonical otherMember
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨names, annotations⟩, compared | ⟨firstLeaf, secondLeaf⟩⟩
    · exact (sound actual.target canonical.target compared).symm
    · have leafLeft : first.leafness = .leaf := by simpa [firstAt] using firstLeaf
      have leafRight : second.leafness = .leaf := by simpa [secondAt] using secondLeaf
      exact (observed_leaves_same term _ _ first second firstAt secondAt
        (firstName.trans (names.symm.trans secondName.symm))
        (firstRefinement.trans (annotations.symm.trans secondRefinement.symm)) leafLeft leafRight).symm
  · rfl

/-- Sparse representative grouping cannot merge two different complete subtrees. -/
theorem sparse_representative_same [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard) :
    Language.Term.atPath term
      (representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) actual) =
      Language.Term.atPath term actual.target := by
  apply representative_same term _ ?_ guard actual member
  intro left right equal
  have complete := sameShape_sound formulas term [] left right true equal
  obtain ⟨subtree, first, second⟩ := (sameTerm_empty_true formulas term left right).mp complete
  exact first.trans second.symm

/-- Complete representative grouping uses the same exact tree-identity invariant. -/
theorem complete_representative_same [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard) :
    Language.Term.atPath term
      (representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) actual) =
      Language.Term.atPath term actual.target := by
  apply representative_same term _ ?_ guard actual member
  intro left right equal
  obtain ⟨subtree, first, second⟩ := (sameTerm_empty_true formulas term left right).mp equal
  exact first.trans second.symm

/-- Equality of sparse representative paths implies equality of complete actual terms. -/
theorem sparse_classes_refine_terms [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (same : representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) first =
      representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) second) :
    Language.Term.atPath term first.target = Language.Term.atPath term second.target := by
  rw [← sparse_representative_same formulas term guard first firstMember,
    ← sparse_representative_same formulas term guard second secondMember, same]

/-- Complete actual comparison is reflexive at every table entry. -/
theorem complete_actual_reflexive [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard) :
    sameTerm formulas term [] actual.target actual.target = some true := by
  obtain ⟨observed, found, _, _⟩ := actual_observed (observe term) guard actual member
  obtain ⟨subtree, atPath, _⟩ := Option.map_eq_some_iff.mp found
  exact (sameTerm_empty_true formulas term _ _).mpr ⟨subtree, atPath, atPath⟩

/-- Equal complete actual subtrees have equal observed names and refinement annotations. -/
theorem actual_labels_equal (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (same : Language.Term.atPath term first.target = Language.Term.atPath term second.target) :
    first.name = second.name ∧ first.refinement = second.refinement := by
  obtain ⟨a, ha, na, ra⟩ := actual_observed (observe term) guard first firstMember
  obtain ⟨b, hb, nb, rb⟩ := actual_observed (observe term) guard second secondMember
  have obs : observe term first.target = observe term second.target := congrArg (Option.map rootObservation) same
  have equal : a = b := Option.some.inj (ha.symm.trans (obs.trans hb))
  subst b
  exact ⟨na.symm.trans nb, ra.symm.trans rb⟩

/-- Complete representative search is canonical for each actual subtree class. -/
theorem complete_representative_canonical [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (same : Language.Term.atPath term first.target = Language.Term.atPath term second.target) :
    representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) first =
      representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) second := by
  have labels := actual_labels_equal term guard first second firstMember secondMember same
  have obs : observe term first.target = observe term second.target := congrArg (Option.map rootObservation) same
  have comparisons : sameTerm formulas term [] first.target = sameTerm formulas term [] second.target := by
    funext other
    simp only [sameTerm, same]
  unfold representative
  simp only [labels.1, labels.2, comparisons, obs]
  split
  · rfl
  · rename_i missing
    have denied := (List.find?_eq_none.mp missing) second secondMember
    have self := complete_actual_reflexive formulas term guard second secondMember
    simp [self] at denied

/-- Sparse actual classes refine the complete source representative classes. -/
theorem sparse_classes_refine_complete [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (same : representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) first =
      representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) second) :
    representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) first =
      representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) second :=
  complete_representative_canonical formulas term guard first second firstMember secondMember
    (sparse_classes_refine_terms formulas term guard first second firstMember secondMember same)

/-- Complete comparison always decides between two existing actual positions. -/
theorem complete_actual_defined [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard) :
    ∃ answer, sameTerm formulas term [] first.target second.target = some answer := by
  obtain ⟨a, ha, _, _⟩ := actual_observed (observe term) guard first firstMember
  obtain ⟨b, hb, _, _⟩ := actual_observed (observe term) guard second secondMember
  obtain ⟨left, hl, _⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨right, hr, _⟩ := Option.map_eq_some_iff.mp hb
  simp [sameTerm, hl, hr]

/-- The complete evaluator never marks an actual identity as ambiguous. -/
theorem complete_ambiguity_empty [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) :
    ambiguous (observe term) (sameTerm formulas term []) guard = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro target member
  obtain ⟨actual, firstMember, _, other, secondMember, _, _, _, unknown, _⟩ :=
    (SourceActuals.ambiguous_iff _ _ _ target).mp member
  obtain ⟨answer, decided⟩ := complete_actual_defined formulas term guard actual other firstMember secondMember
  simp [unknown] at decided

/-- Equal leaf observations make sparse representative search canonical. -/
theorem sparse_leaf_canonical [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (same : Language.Term.atPath term first.target = Language.Term.atPath term second.target)
    (leaf : (observe term first.target).map Observed.leafness = some .leaf) :
    representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) first =
      representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) second := by
  have labels := actual_labels_equal term guard first second firstMember secondMember same
  have obs : observe term first.target = observe term second.target := congrArg (Option.map rootObservation) same
  have comparisons : sameShape formulas (observe term) [] first.target = sameShape formulas (observe term) [] second.target := by
    funext other
    simp only [sameShape, obs]
  have otherLeaf : (observe term second.target).map Observed.leafness = some .leaf := obs ▸ leaf
  unfold representative
  simp only [labels.1, labels.2, comparisons, obs]
  split
  · rfl
  · rename_i missing
    have denied := (List.find?_eq_none.mp missing) second secondMember
    simp [otherLeaf] at denied

/-- Equal inner actual terms at different positions are explicitly recorded as ambiguous. -/
theorem equal_inner_ambiguous [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (same : Language.Term.atPath term first.target = Language.Term.atPath term second.target)
    (different : first.target ≠ second.target)
    (inner : (observe term first.target).map Observed.leafness ≠ some .leaf) :
    first.target ∈ ambiguous (observe term) (sameShape formulas (observe term) []) guard := by
  have labels := actual_labels_equal term guard first second firstMember secondMember same
  obtain ⟨observed, found, _, _⟩ := actual_observed (observe term) guard first firstMember
  obtain ⟨subtree, atPath, root⟩ := Option.map_eq_some_iff.mp found
  have secondPath : Language.Term.atPath term second.target = some subtree := same.symm.trans atPath
  have unknown : sameShape formulas (observe term) [] first.target second.target = none := by
    cases subtree with
    | node label children =>
        cases children with
        | nil => simp [observe, atPath, rootObservation] at inner
        | cons child rest =>
            simp [sameShape, observe, atPath, secondPath, rootObservation, renameObserved, renameRoot, compareObserved]
  exact (SourceActuals.ambiguous_iff _ _ _ first.target).mpr
    ⟨first, firstMember, rfl, second, secondMember, different, labels.1, labels.2, unknown, Or.inl inner⟩

/-- Without an ambiguity witness, sparse classes also identify every equal complete actual term. -/
theorem unambiguous_classes_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = []) :
    representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) first =
      representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) second ↔
    Language.Term.atPath term first.target = Language.Term.atPath term second.target := by
  constructor
  · exact sparse_classes_refine_terms formulas term guard first second firstMember secondMember
  · intro same
    by_cases leaf : (observe term first.target).map Observed.leafness = some .leaf
    · exact sparse_leaf_canonical formulas term guard first second firstMember secondMember same leaf
    · by_cases positions : first.target = second.target
      · have labels := actual_labels_equal term guard first second firstMember secondMember same
        have equal : first = second := by cases first; cases second; simp_all
        rw [equal]
      · have impossible := equal_inner_ambiguous formulas term guard first second firstMember secondMember same positions leaf
        simp [unambiguous] at impossible

/-- A representative path comes from an actual table entry, including the fallback. -/
theorem representative_member [DecidableEq Formula] (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (entries : List (Actual Formula)) (actual : Actual Formula)
    (member : actual ∈ entries) :
    ∃ chosen ∈ entries, representative observed sameAt entries actual = chosen.target := by
  unfold representative
  split
  · rename_i canonical selected
    exact ⟨canonical, List.mem_of_find?_eq_some selected, rfl⟩
  · exact ⟨actual, member, rfl⟩

/-- An unambiguous inner actual has no distinct position with the same complete subtree. -/
theorem unambiguous_inner_unique [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (firstMember : first ∈ actuals (observe term) guard) (secondMember : second ∈ actuals (observe term) guard)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = [])
    (inner : (observe term first.target).map Observed.leafness ≠ some .leaf)
    (same : Language.Term.atPath term first.target = Language.Term.atPath term second.target) :
    first.target = second.target := by
  by_cases different : first.target = second.target
  · exact different
  · have impossible := equal_inner_ambiguous formulas term guard first second firstMember secondMember same different inner
    simp [unambiguous] at impossible

/-- Comparing a complete leaf with any complete term needs only the root observation. -/
theorem compare_leaf_complete [DecidableEq Formula] (label : Label Formula) (other : Language.Term (Label Formula)) :
    compareObserved (rootObservation (.node label [])) (rootObservation other) =
      some (Language.termEq (.node label []) other) := by
  cases other with
  | node otherLabel children =>
      by_cases labels : label = otherLabel
      · subst otherLabel
        cases children with
        | nil => simp [compareObserved, rootObservation, (Language.termEq_correct _ _).mpr rfl]
        | cons child rest =>
            have unequal : Language.termEq (.node label []) (.node label (child :: rest)) = false := by
              apply Bool.eq_false_iff.mpr
              intro equal
              have impossible := (Language.termEq_correct _ _).mp equal
              cases impossible
            simp [compareObserved, rootObservation, unequal]
      · have unequal : Language.termEq (.node label []) (.node otherLabel children) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact labels (Language.Term.node.inj ((Language.termEq_correct _ _).mp equal)).1
        simp [compareObserved, rootObservation, labels, unequal]

/-- The sparse and complete equality callbacks agree whenever the first observed term is a leaf. -/
theorem leaf_callbacks_equal [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (left right : Path)
    (leaf : (observe term left).map Observed.leafness = some .leaf) :
    sameShape formulas (observe term) [] left right = sameTerm formulas term [] left right := by
  cases hl : Language.Term.atPath term left with
  | none => simp [observe, hl] at leaf
  | some subtree =>
      cases subtree with
      | node label children =>
          cases children with
          | cons child rest => simp [observe, hl, rootObservation] at leaf
          | nil =>
              cases hr : Language.Term.atPath term right with
              | none => simp [sameShape, sameTerm, observe, hl, hr]
              | some other =>
                  simpa only [sameShape, sameTerm, observe, hl, hr, Option.map_some,
                    Bind.bind, Option.bind, Pure.pure, renameObserved, renameRoot, List.foldl_nil,
                    renameTree_empty] using compare_leaf_complete label other

/-- If the sparse ambiguity set is empty, both source searches choose the same representative path. -/
theorem unambiguous_representative_equal [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = []) :
    representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) actual =
      representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) actual := by
  by_cases leaf : (observe term actual.target).map Observed.leafness = some .leaf
  · unfold representative
    have callbacks : sameShape formulas (observe term) [] actual.target = sameTerm formulas term [] actual.target :=
      funext (fun other => leaf_callbacks_equal formulas term actual.target other leaf)
    rw [callbacks]
  · obtain ⟨sparse, sparseMember, sparsePath⟩ := representative_member (observe term)
      (sameShape formulas (observe term) []) _ actual member
    obtain ⟨complete, completeMember, completePath⟩ := representative_member (observe term)
      (sameTerm formulas term []) _ actual member
    have sparseSame := sparse_representative_same formulas term guard actual member
    have completeSame := complete_representative_same formulas term guard actual member
    rw [sparsePath] at sparseSame
    rw [completePath] at completeSame
    have sparsePosition := unambiguous_inner_unique formulas term guard actual sparse member sparseMember
      unambiguous leaf sparseSame.symm
    have completePosition := unambiguous_inner_unique formulas term guard actual complete member completeMember
      unambiguous leaf completeSame.symm
    rw [sparsePath, completePath, ← sparsePosition, ← completePosition]

/-- Unambiguous sparse allocation computes exactly the complete evaluator's declaration and ambiguity tables. -/
theorem unambiguous_tables_equal [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = []) :
    substitutionValues formulas (observe term) (sameShape formulas (observe term) []) guard =
      substitutionValues formulas (observe term) (sameTerm formulas term []) guard := by
  have valuesSame : values (observe term) (sameShape formulas (observe term) []) guard =
      values (observe term) (sameTerm formulas term []) guard := by
    simp only [values]
    apply congrArg List.eraseDups
    apply List.map_congr_left
    intro actual member
    rw [unambiguous_representative_equal formulas term guard actual member unambiguous]
  have conflictsSame : conflicts (observe term) (sameShape formulas (observe term) []) guard =
      conflicts (observe term) (sameTerm formulas term []) guard := by unfold conflicts; rw [valuesSame]
  have allocatedSame : allocated formulas (observe term) (sameShape formulas (observe term) []) guard =
      allocated formulas (observe term) (sameTerm formulas term []) guard := by unfold allocated; rw [conflictsSame]
  unfold substitutionValues
  rw [allocatedSame, unambiguous, complete_ambiguity_empty]
  dsimp only
  congr 1
  apply filterMap_congr
  intro actual member
  rw [unambiguous_representative_equal formulas term guard actual member unambiguous]

end MicroCFTA.ActualQuotient
