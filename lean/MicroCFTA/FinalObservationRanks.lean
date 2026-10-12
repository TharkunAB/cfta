import MicroCFTA.OpenGroupedApplication

/-!
# Final finite observation groups and rank callbacks

The finite merge keeps a positive singleton unchanged. A larger merge adds one
private Choice layer. Its offsets use child cardinalities. This module follows
the selector and all three source callback views through repeated merges.
-/
namespace MicroCFTA.FinalObservationRanks
open Language GeneratorCombinators IntegerTermViews

/-- The fields used by finite observation regrouping. -/
structure Index (Symbol : Type) where
  count : Nat
  select : Nat → Option (Term (Label Symbol))
  ranks : View → List (Term (Label Symbol)) → List Nat

/-- Each callback returns all replay positions with the requested view. -/
structure Exact (index : Index Symbol) : Prop where
  bounds : ∀ rank, (∃ term, index.select rank = some term) ↔ rank < index.count
  ranks : ∀ view wanted rank, rank ∈ index.ranks view wanted ↔
    ∃ term, index.select rank = some term ∧ project view term = wanted

/-- Source Choice wrappers remain visible in whole and spine views. -/
theorem choice_project (branch : Nat) (term : Term (Label Symbol)) (view : View) :
    project view (.node (.choice branch) [term]) =
      match view with
      | .whole | .spine => [.node (.choice branch) [term]]
      | .labelled => project .labelled term := by
  cases view <;> simp [project, labelled, spine, SupportTerms.applicationTermChildren,
    SupportTerms.applicationLeftChildren]

/-- Read the source child view for one local frequency branch. -/
def childView (branch : Nat) : View → List (Term (Label Symbol)) → Option (View × List (Term (Label Symbol)))
  | .labelled, wanted => some (.labelled, wanted)
  | .whole, [.node (.choice found) [term]] | .spine, [.node (.choice found) [term]] =>
      if found = branch then some (.whole, [term]) else none
  | _, _ => none

/-- The branch dispatch is exactly the view of its selected private wrapper. -/
theorem childView_exact (branch : Nat) (view : View) (wanted : List (Term (Label Symbol)))
    (term : Term (Label Symbol)) :
    (∃ next, childView branch view wanted = some next ∧ project next.1 term = next.2) ↔
      project view (.node (.choice branch) [term]) = wanted := by
  rw [choice_project]
  cases view with
  | labelled => simp [childView]
  | whole | spine =>
      constructor
      · rintro ⟨next, chosen, matched⟩
        simp only [childView] at chosen
        split at chosen <;> simp_all [project]
        rcases chosen with ⟨rfl, rfl⟩
        simpa using matched
      · intro same
        subst wanted
        exact ⟨(.whole, [term]), by simp [childView], rfl⟩

/-- Source branchRanks adds the cumulative cardinality offset. -/
def branchRanks (index : Index Symbol) (branch start : Nat) (view : View)
    (wanted : List (Term (Label Symbol))) : List Nat :=
  match childView branch view wanted with
  | none => []
  | some next => (index.ranks next.1 next.2).map (start + ·)

/-- A branch callback preserves precisely the selected child views. -/
theorem branchRanks_exact (index : Index Symbol) (exact : Exact index) (branch start : Nat)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat) :
    rank ∈ branchRanks index branch start view wanted ↔
      ∃ childRank term, index.select childRank = some term ∧ rank = start + childRank ∧
        project view (.node (.choice branch) [term]) = wanted := by
  constructor
  · intro member
    unfold branchRanks at member
    cases found : childView branch view wanted with
    | none => simp [found] at member
    | some next =>
        obtain ⟨childRank, member, same⟩ := List.mem_map.mp (by simpa [found] using member)
        obtain ⟨term, selected, matched⟩ := (exact.ranks next.1 next.2 childRank).mp member
        exact ⟨childRank, term, selected, same.symm, (childView_exact branch view wanted term).mp ⟨next, found, matched⟩⟩
  · rintro ⟨childRank, term, selected, rfl, matched⟩
    obtain ⟨next, found, matched⟩ := (childView_exact branch view wanted term).mpr matched
    simp only [branchRanks, found]
    exact List.mem_map.mpr ⟨childRank, (exact.ranks next.1 next.2 childRank).mpr ⟨term, selected, matched⟩, rfl⟩

/-- Sum all finite child counts, including empty children. -/
def totalCount (indexes : List (Index Symbol)) : Nat := (indexes.map Index.count).sum

/-- Source selectBranch scans consecutive half-open rank intervals. -/
def selectBranches (first : Nat) : List (Index Symbol) → Nat → Option (Term (Label Symbol))
  | [], _ => none
  | index :: rest, rank =>
      if rank < index.count then (index.select rank).map (fun term => .node (.choice first) [term])
      else selectBranches (first + 1) rest (rank - index.count)

/-- Source choiceRanks preserves branch order and rebases each child callback. -/
def frequencyRanks (first start : Nat) : List (Index Symbol) → View → List (Term (Label Symbol)) → List Nat
  | [], _, _ => []
  | index :: rest, view, wanted => branchRanks index first start view wanted ++
      frequencyRanks (first + 1) (start + index.count) rest view wanted

/-- The selector succeeds on exactly the sum of the finite child intervals. -/
theorem selectBranches_bounds (indexes : List (Index Symbol))
    (correct : ∀ index ∈ indexes, Exact index) (first rank : Nat) :
    (∃ term, selectBranches first indexes rank = some term) ↔ rank < totalCount indexes := by
  induction indexes generalizing first rank with
  | nil => simp [selectBranches, totalCount]
  | cons index rest ih =>
      have current := correct index (by simp)
      have tail := ih (fun child member => correct child (by simp [member]))
      by_cases inside : rank < index.count
      · obtain ⟨term, selected⟩ := (current.bounds rank).mpr inside
        simp [selectBranches, inside, selected, totalCount, Nat.lt_add_right _ inside]
      · rw [selectBranches, ite_eq_right inside, tail]
        simp only [totalCount, List.map_cons, List.sum_cons]
        omega

/-- Callback offsets and selector subtraction describe the same complete interval. -/
theorem frequencyRanks_exact (indexes : List (Index Symbol))
    (correct : ∀ index ∈ indexes, Exact index) (first start : Nat)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat) :
    rank ∈ frequencyRanks first start indexes view wanted ↔
      ∃ childRank term, rank = start + childRank ∧
        selectBranches first indexes childRank = some term ∧ project view term = wanted := by
  induction indexes generalizing first start rank with
  | nil => simp [frequencyRanks, selectBranches]
  | cons index rest ih =>
      have current := correct index (by simp)
      have tail := ih (fun child member => correct child (by simp [member]))
      rw [frequencyRanks, List.mem_append, branchRanks_exact index current, tail]
      constructor
      · rintro (⟨childRank, term, selected, same, matched⟩ | ⟨childRank, term, same, selected, matched⟩)
        · have inside := (current.bounds childRank).mp ⟨term, selected⟩
          exact ⟨childRank, .node (.choice first) [term], same, by simp [selectBranches, inside, selected], matched⟩
        · refine ⟨index.count + childRank, term, by omega, ?_, matched⟩
          simpa [selectBranches, show ¬index.count + childRank < index.count by omega] using selected
      · rintro ⟨childRank, term, same, selected, matched⟩
        by_cases inside : childRank < index.count
        · simp only [selectBranches, inside, ↓reduceIte, Option.map_eq_some_iff] at selected
          obtain ⟨child, selected, rfl⟩ := selected
          exact Or.inl ⟨childRank, child, selected, same, matched⟩
        · exact Or.inr ⟨childRank - index.count, term, by omega,
            by simpa [selectBranches, inside] using selected, matched⟩

/-- Construct one actual frequencyStatic rank record. -/
def frequency (indexes : List (Index Symbol)) : Index Symbol :=
  ⟨totalCount indexes, selectBranches 0 indexes, frequencyRanks 0 0 indexes⟩

/-- Finite frequency construction derives its full rank invariant from the child records. -/
theorem frequency_exact (indexes : List (Index Symbol)) (correct : ∀ index ∈ indexes, Exact index) :
    Exact (frequency indexes) := by
  refine ⟨selectBranches_bounds indexes correct 0, ?_⟩
  intro view wanted rank
  simpa [frequency] using frequencyRanks_exact indexes correct 0 0 view wanted rank


/-- Select the actual original-times-point term after the parent label adapter. -/
def pointSelect (literal : Int → Symbol) (specialize : List Int → Symbol → Symbol)
    (symbol : Symbol) (source : OpenGroupedApplication.Source Value) (points : LatticeAPI.Points)
    (rank : Nat) : Option (Term (Label Symbol)) :=
  if inside : rank < OpenGroupedApplication.cardinality source * LatticeSelect.pointCount points.levels then do
    let original ← OpenGroupedApplication.select source (rank / LatticeSelect.pointCount points.levels)
    let pointRank : Fin (LatticeSelect.pointCount points.levels) :=
      ⟨rank % LatticeSelect.pointCount points.levels, (Probability.split_lt inside).2⟩
    pure (fill literal specialize (LatticeSelect.decode points.dimension points.levels pointRank)
      (SupportTerms.labelTerm symbol original)).2
  else none

/-- Product selection uses the same original and point radices as pointsStatic. -/
theorem pointSelect_selected (literal : Int → Symbol) (specialize : List Int → Symbol → Symbol)
    (symbol : Symbol) {source : OpenGroupedApplication.Source Value} {originalRank : Nat}
    {term : Term (Label Symbol)} (selected : OpenGroupedApplication.Selected source originalRank term)
    (points : LatticeAPI.Points) (pointRank : Fin (LatticeSelect.pointCount points.levels)) :
    pointSelect literal specialize symbol source points
      (Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank.val) =
      some (fill literal specialize (LatticeSelect.decode points.dimension points.levels pointRank)
        (SupportTerms.labelTerm symbol term)).2 := by
  have inside := Probability.pairRank_lt (OpenGroupedApplication.selected_bound selected) pointRank.isLt
  have split := Probability.split_pair (left := originalRank) pointRank.isLt
  simp only [Probability.splitRank, Prod.mk.injEq] at split
  simp [pointSelect, inside, split.1, split.2, OpenGroupedApplication.selected_select selected]

/-- A successful replay exposes a valid original and one exact point rank. -/
theorem pointSelect_sound (literal : Int → Symbol) (specialize : List Int → Symbol → Symbol)
    (symbol : Symbol) (source : OpenGroupedApplication.Source Value) (points : LatticeAPI.Points)
    (rank : Nat) (term : Term (Label Symbol))
    (selected : pointSelect literal specialize symbol source points rank = some term) :
    ∃ originalRank original, OpenGroupedApplication.Selected source originalRank original ∧
      ∃ pointRank : Fin (LatticeSelect.pointCount points.levels),
        rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank.val ∧
        term = (fill literal specialize (LatticeSelect.decode points.dimension points.levels pointRank)
          (SupportTerms.labelTerm symbol original)).2 := by
  unfold pointSelect at selected
  split at selected
  · rename_i inside
    cases found : OpenGroupedApplication.select (Symbol := Symbol) source
      (rank / LatticeSelect.pointCount points.levels) with
    | none => simp [found] at selected
    | some original =>
        refine ⟨_, original, (OpenGroupedApplication.select_exact source _ original).mp found,
          ⟨_, (Probability.split_lt inside).2⟩, (Probability.pair_split _ rank).symm, ?_⟩
        simpa [found, Probability.splitRank] using selected.symm
  · cases selected

/-- The concrete seed record uses source candidate discovery and exact point validation. -/
def pointIndex [DecidableEq Symbol] (literal : Int → Symbol) (specialize : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (source : OpenGroupedApplication.Source Value) (points : LatticeAPI.Points) : Index Symbol :=
  ⟨OpenGroupedApplication.cardinality source * LatticeSelect.pointCount points.levels,
    pointSelect literal specialize symbol source points,
    OpenGroupedApplication.parentPointCandidates literal specialize read symbol acceptsLabel source points⟩

/-- Generated integer sources supply the full seed invariant; no term-codec inverse is assumed. -/
theorem pointIndex_exact [DecidableEq Symbol] (literal : Int → Symbol) (specialize : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (compatible : ∀ point, acceptsLabel (specialize point symbol) = true)
    (source : OpenGroupedApplication.Source Value) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (OpenIntegerKeys.names (OpenGroupedApplication.width source))
      (FullSyntax.lowerFormula formula) = .ok points) :
    Exact (pointIndex literal specialize read symbol acceptsLabel source points) := by
  constructor
  · intro rank
    constructor
    · rintro ⟨term, selected⟩
      obtain ⟨originalRank, original, originalSelected, pointRank, rfl, _⟩ :=
        pointSelect_sound literal specialize symbol source points rank term selected
      exact Probability.pairRank_lt (OpenGroupedApplication.selected_bound originalSelected) pointRank.isLt
    · intro inside
      obtain ⟨original, selected⟩ := OpenGroupedApplication.selected_exists source
        (rank / LatticeSelect.pointCount points.levels) (Probability.split_lt inside).1
      let pointRank : Fin (LatticeSelect.pointCount points.levels) :=
        ⟨rank % LatticeSelect.pointCount points.levels, (Probability.split_lt inside).2⟩
      have replay := pointSelect_selected literal specialize symbol selected points pointRank
      rw [show Probability.pairRank (LatticeSelect.pointCount points.levels)
        (rank / LatticeSelect.pointCount points.levels) pointRank.val = rank from Probability.pair_split _ rank] at replay
      exact ⟨_, replay⟩
  · intro view wanted rank
    constructor
    · intro member
      obtain ⟨originalRank, original, selected, pointRank, rfl, same⟩ :=
        OpenGroupedApplication.parent_points_sound literal specialize read symbol acceptsLabel source _ formula points built
          view wanted rank member
      exact ⟨_, pointSelect_selected literal specialize symbol selected points pointRank, same⟩
    · rintro ⟨term, selected, rfl⟩
      obtain ⟨originalRank, original, originalSelected, pointRank, rfl, rfl⟩ :=
        pointSelect_sound literal specialize symbol source points rank term selected
      exact OpenGroupedApplication.parent_points_complete literal specialize read literalRead symbol acceptsLabel compatible
        originalSelected formula points built view pointRank

/-- Current source settlement supplies the actual successful lattice query and integer matcher law. -/
theorem settledIndex_exact
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol)
    (specialized : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol))
    (parents : List FullSyntax.Formula) (bucket : OpenGroupedApplication.Bucket Value)
    (closed : OpenGroupedApplication.ClosedBucket Value)
    (success : OpenGroupedApplication.settle parents bucket = .ok (some closed)) :
    Exact (pointIndex IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue symbol
      (IntegerLabelCodec.fills symbol) bucket.source closed.points) :=
  pointIndex_exact IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
    IntegerLabelCodec.leafValue_integer symbol (IntegerLabelCodec.fills symbol)
    (fun point => IntegerLabelCodec.exactLabel_matches point symbol _ (specialized point)) bucket.source
    (OpenGroupedApplication.parentFormula bucket.source parents) closed.points
    (OpenGroupedApplication.settle_fields parents bucket closed success).2.2.1

/-- Rank projection of mergeBucketGroup on its nonempty positive success domain. -/
def mergeIndex : List (Index Symbol) → Index Symbol
  | [index] => index
  | indexes => frequency indexes

/-- A successful singleton merge does not insert a Choice wrapper. -/
theorem merge_singleton (index : Index Symbol) : mergeIndex [index] = index := rfl

/-- Every finite merge preserves complete inverse rank queries. -/
theorem merge_exact (indexes : List (Index Symbol)) (correct : ∀ index ∈ indexes, Exact index) :
    Exact (mergeIndex indexes) := by
  unfold mergeIndex
  split
  · exact correct _ (by simp)
  · exact frequency_exact _ correct

/-- The source singleton fast path and the general path retain the same total count. -/
theorem merge_count (indexes : List (Index Symbol)) : (mergeIndex indexes).count = totalCount indexes := by
  unfold mergeIndex
  split <;> simp [frequency, totalCount]

/-- Regroup finite records by the current observation key and merge each group in map order. -/
def regroup [DecidableEq Key] (before : Key → Key → Bool) (key : Index Symbol → Key)
    (indexes : List (Index Symbol)) : List (Index Symbol) :=
  (GeneratorCombinators.groupOutcomes before key indexes).map mergeIndex

/-- Every record produced by observation regrouping has exact callbacks. -/
theorem regroup_exact [DecidableEq Key] (before : Key → Key → Bool) (key : Index Symbol → Key)
    (indexes : List (Index Symbol)) (correct : ∀ index ∈ indexes, Exact index)
    (result : Index Symbol) (member : result ∈ regroup before key indexes) : Exact result := by
  obtain ⟨group, grouped, rfl⟩ := List.mem_map.mp member
  apply merge_exact
  intro index present
  apply correct index
  exact (GeneratorCombinators.groupOutcomes_perm before key indexes).mem_iff.mp
    (List.mem_flatten.mpr ⟨group, grouped, present⟩)

/-- Grouping does not change the total number of member positions. -/
theorem regroup_count [DecidableEq Key] (before : Key → Key → Bool) (key : Index Symbol → Key)
    (indexes : List (Index Symbol)) : totalCount (regroup before key indexes) = totalCount indexes := by
  have sumFlatten : ∀ groups : List (List (Index Symbol)),
      (groups.map totalCount).sum = totalCount groups.flatten := by
    intro groups
    induction groups with
    | nil => rfl
    | cons group rest ih =>
        change totalCount group + (rest.map totalCount).sum = totalCount (group ++ rest.flatten)
        rw [ih]
        simp only [totalCount, List.map_append, List.sum_append]
  simp only [regroup, totalCount, List.map_map, Function.comp_def, merge_count]
  change ((GeneratorCombinators.groupOutcomes before key indexes).map totalCount).sum = totalCount indexes
  rw [sumFlatten]
  exact ((GeneratorCombinators.groupOutcomes_perm before key indexes).map Index.count).sum_nat

/-- Final ungroup merges every observation bucket into the one unit-key bucket. -/
def ungroup (indexes : List (Index Symbol)) : Index Symbol := mergeIndex indexes

/-- Nested observation merging and final ungroup preserve all rank preimages in every view. -/
theorem final_exact [DecidableEq Key] (before : Key → Key → Bool) (key : Index Symbol → Key)
    (indexes : List (Index Symbol)) (correct : ∀ index ∈ indexes, Exact index) :
    Exact (ungroup (regroup before key indexes)) :=
  merge_exact _ (regroup_exact before key indexes correct)

/-- The final global rank interval has the sum of all original-times-point counts. -/
theorem final_count [DecidableEq Key] (before : Key → Key → Bool) (key : Index Symbol → Key)
    (indexes : List (Index Symbol)) :
    (ungroup (regroup before key indexes)).count = totalCount indexes := by
  rw [ungroup, merge_count, regroup_count]


/-- Each source branch has its exact local Choice index and cumulative count offset. -/
theorem selectBranches_member (first : Nat) (before after : List (Index Symbol)) (index : Index Symbol)
    (rank : Nat) (term : Term (Label Symbol)) (inside : rank < index.count)
    (selected : index.select rank = some term) :
    selectBranches first (before ++ index :: after) (totalCount before + rank) =
      some (.node (.choice (first + before.length)) [term]) := by
  induction before generalizing first with
  | nil => simp [totalCount, selectBranches, inside, selected]
  | cons current before ih =>
      have outside' : ¬current.count + ((before.map Index.count).sum + rank) < current.count := by omega
      simpa [totalCount, selectBranches, Nat.add_assoc, outside', Nat.add_comm 1 before.length] using ih (first + 1)

/-- The positive singleton path is the only merge that omits the source Choice wrapper. -/
theorem mergeIndex_member (before after : List (Index Symbol)) (index : Index Symbol)
    (rank : Nat) (term : Term (Label Symbol)) (inside : rank < index.count)
    (selected : index.select rank = some term) :
    (mergeIndex (before ++ index :: after)).select (totalCount before + rank) =
      some (if before.isEmpty && after.isEmpty then term else .node (.choice before.length) [term]) := by
  by_cases singleton : before = [] ∧ after = []
  · rcases singleton with ⟨rfl, rfl⟩
    simpa [mergeIndex, totalCount] using selected
  · have many : ∀ only, before ++ index :: after ≠ [only] := by
      intro only equal
      have lengths := congrArg List.length equal
      have left : before = [] := List.length_eq_zero_iff.mp (by simp at lengths; omega)
      have right : after = [] := List.length_eq_zero_iff.mp (by simp at lengths; omega)
      exact singleton ⟨left, right⟩
    have wrapped := selectBranches_member 0 before after index rank term inside selected
    simp only [Nat.zero_add] at wrapped
    simpa [mergeIndex, many, frequency, Bool.and_eq_true, List.isEmpty_iff, singleton] using wrapped

/-- Each existing member gets a distinct position in the merged interval, independent of its view or value. -/
theorem branch_intervals_disjoint (before middle : List (Index Symbol)) (left : Index Symbol)
    (leftRank rightRank : Nat) (leftInside : leftRank < left.count) :
    totalCount before + leftRank ≠ totalCount (before ++ left :: middle) + rightRank := by
  simp only [totalCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  omega


/-- Constant observation regrouping produces the one source bucket in its original order. -/
theorem unit_group (items : List Item) :
    GeneratorCombinators.groupOutcomes (fun (_ _ : Unit) => true) (fun (_ : Item) => ()) items =
      if items.isEmpty then [] else [items] := by
  cases items with
  | nil => simp [GeneratorCombinators.groupOutcomes, Sized.groups]
  | cons first rest =>
      have yes : rest.filter (fun _ => true) = rest := by
        induction rest <;> simp_all
      have no : rest.filter (fun _ => false) = [] := by
        induction rest <;> simp_all
      simp [GeneratorCombinators.groupOutcomes, Sized.groups, yes, no]

/-- Finite public ungroup is precisely the unit-key regroup and lookup. -/
theorem ungroup_source (indexes : List (Index Symbol)) (nonempty : indexes ≠ []) :
    (regroup (fun (_ _ : Unit) => true) (fun (_ : Index Symbol) => ()) indexes).head? =
      some (ungroup indexes) := by
  simp [regroup, unit_group, List.isEmpty_eq_false_iff.mpr nonempty, ungroup]

end MicroCFTA.FinalObservationRanks



