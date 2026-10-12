import MicroCFTA.RecursiveCallbackTermination

/-!
# Distinct positions from recursive source callbacks

Position distinctness is stronger than membership correctness. The proof
uses each producer's actual list and the injective source rank arithmetic.
Unchecked rows satisfy the same interval and distinctness requirements.
-/
namespace MicroCFTA.RecursiveCallbackDistinct
open Language GeneratorCombinators IntegerTermViews SizedRank RecursiveCallbackTermination

/-- Different callback rows have different size-class positions. -/
def Distinct (rows : List Checked) : Prop := rows.Pairwise (fun a b => a.1 ≠ b.1)

/-- The row property is exactly duplicate-free public positions. -/
theorem distinct_iff (rows : List Checked) : Distinct rows ↔ (rows.map Prod.fst).Nodup := by
  simp only [Distinct, List.Nodup, List.pairwise_map]

/-- Permuting complete rows preserves position distinctness. -/
theorem distinct_perm (first second : List Checked) (permutation : first.Perm second)
    (distinct : Distinct first) : Distinct second := by
  rw [distinct_iff] at distinct ⊢
  exact (permutation.map Prod.fst).nodup_iff.mp distinct

/-- Source sorting keeps exactly the original position multiplicities. -/
theorem sorted_distinct (rows : List Checked) (distinct : Distinct rows) : Distinct (sorted rows) :=
  distinct_perm rows (sorted rows) (List.mergeSort_perm rows before).symm distinct

/-- A common paid size increment cannot identify two positions. -/
theorem pay_distinct (rows : List Checked) (distinct : Distinct rows) :
    Distinct (RecursiveCheckedRanks.payRows rows) := by
  rw [Distinct, RecursiveCheckedRanks.payRows, List.pairwise_map]
  apply distinct.imp
  intro a b different same
  apply different
  have sizes := congrArg Position.size same
  have ranks := congrArg Position.rank same
  rcases a with ⟨⟨_, _⟩, _⟩
  rcases b with ⟨⟨_, _⟩, _⟩
  simp_all

/-- A size-dependent choice offset is injective on positions. -/
theorem choice_injective (left right : Nat → Nat) (a b : Checked)
    (same : (RecursiveCheckedRanks.choiceRow [left, right] 1 a).1 =
      (RecursiveCheckedRanks.choiceRow [left, right] 1 b).1) : a.1 = b.1 := by
  have sizes := congrArg Position.size same
  have ranks := congrArg Position.rank same
  simp [RecursiveCheckedRanks.choiceRow, choicePosition] at sizes ranks
  rcases a with ⟨⟨_, _⟩, _⟩
  rcases b with ⟨⟨_, _⟩, _⟩
  simp_all

/-- Shifting one choice branch keeps its positions distinct. -/
theorem choice_distinct (left right : Nat → Nat) (rows : List Checked) (distinct : Distinct rows) :
    Distinct (rows.map (RecursiveCheckedRanks.choiceRow [left, right] 1)) := by
  rw [Distinct, List.pairwise_map]
  exact distinct.imp (fun different same => different (choice_injective left right _ _ same))

/-- Earlier and shifted later alternatives occupy disjoint class intervals. -/
theorem choices_distinct (left right : Nat → Nat) (first second : List Checked)
    (firstDistinct : Distinct first) (secondDistinct : Distinct second)
    (firstValid : ∀ row ∈ first, row.1.rank < left row.1.size) :
    Distinct (first ++ second.map (RecursiveCheckedRanks.choiceRow [left, right] 1)) := by
  rw [Distinct, List.pairwise_append]
  refine ⟨firstDistinct, choice_distinct left right second secondDistinct, ?_⟩
  intro a am b bm same
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp bm
  have within := firstValid a am
  have sizes := congrArg Position.size same
  have ranks := congrArg Position.rank same
  simp [RecursiveCheckedRanks.choiceRow, choicePosition] at sizes ranks
  rw [sizes] at within
  omega

/-- A valid source product position determines both original positions. -/
theorem product_injective (left right : Nat → Nat) (a b c d : Position)
    (av : a.rank < left a.size) (bv : b.rank < right b.size)
    (cv : c.rank < left c.size) (dv : d.rank < right d.size)
    (same : productPosition left right a b = productPosition left right c d) : a = c ∧ b = d := by
  have split := congrArg (productSplit left right) same
  rw [productSplit_productPosition left right a b av bv,
    productSplit_productPosition left right c d cv dv] at split
  exact Prod.mk.inj (Option.some.inj split)

/-- Cartesian callback rows cannot repeat a valid source product position. -/
theorem product_distinct (left right : Nat → Nat) (first second : List Checked)
    (firstDistinct : Distinct first) (secondDistinct : Distinct second)
    (firstValid : ∀ row ∈ first, row.1.rank < left row.1.size)
    (secondValid : ∀ row ∈ second, row.1.rank < right row.1.size) :
    Distinct (RecursiveCheckedRanks.productRows left right first second) := by
  rw [Distinct, RecursiveCheckedRanks.productRows, List.pairwise_flatMap]
  constructor
  · intro a am
    rw [List.pairwise_map]
    exact secondDistinct.imp_of_mem (fun bm dm different same => different
      (product_injective left right a.1 _ a.1 _ (firstValid a am) (secondValid _ bm)
        (firstValid a am) (secondValid _ dm) same).2)
  · apply firstDistinct.imp_of_mem
    intro a c am cm different x xm y ym same
    obtain ⟨b, bm, rfl⟩ := List.mem_map.mp xm
    obtain ⟨d, dm, rfl⟩ := List.mem_map.mp ym
    exact different (product_injective left right a.1 b.1 c.1 d.1
      (firstValid a am) (secondValid b bm) (firstValid c cm) (secondValid d dm) same).1

/-- Every finite leaf has distinct source positions before the recursive knot is tied. -/
def LeavesDistinct : Recipe Symbol → Prop
  | .finite source => ∀ view wanted, Distinct (source.positions view wanted)
  | .occurrence => True
  | .map inner | .pay inner | .label _ inner => LeavesDistinct inner
  | .choice left right | .ap left right => LeavesDistinct left ∧ LeavesDistinct right

/-- Every view of an arbitrary recursive source has distinct candidate positions. -/
theorem positions_distinct [DecidableEq Symbol] (self : Nat → Nat) (body : Recipe Symbol)
    (bodyCounts : ∀ size, self size = counts self body size)
    (bodyBounded : LeavesBounded body) (bodyDistinct : LeavesDistinct body)
    (recipe : Recipe Symbol) (bounded : LeavesBounded recipe) (distinct : LeavesDistinct recipe)
    (view : View) (wanted : List (EngineTerm Symbol)) : Distinct (positions self body recipe view wanted) := by
  cases recipe with
  | finite source => rw [positions]; exact distinct view wanted
  | occurrence =>
      rw [positions.eq_def]
      dsimp only
      split
      · rename_i term
        exact positions_distinct self body bodyCounts bodyBounded bodyDistinct body bodyBounded bodyDistinct .whole [term]
      · exact .nil
  | map inner =>
      rw [positions]
      exact positions_distinct self body bodyCounts bodyBounded bodyDistinct inner bounded distinct view wanted
  | pay inner =>
      rw [positions]
      exact pay_distinct _ (positions_distinct self body bodyCounts bodyBounded bodyDistinct inner bounded distinct view wanted)
  | choice left right =>
      rw [positions.eq_def]
      apply sorted_distinct
      cases view with
      | labelled =>
          exact choices_distinct _ _ _ _
            (positions_distinct self body bodyCounts bodyBounded bodyDistinct left bounded.1 distinct.1 .labelled wanted)
            (positions_distinct self body bodyCounts bodyBounded bodyDistinct right bounded.2 distinct.2 .labelled wanted)
            (positions_bound self body bodyCounts bodyBounded left bounded.1 .labelled wanted)
      | whole | spine =>
          dsimp only
          split
          · rename_i child
            exact positions_distinct self body bodyCounts bodyBounded bodyDistinct left bounded.1 distinct.1 .whole [child]
          · rename_i child
            exact choice_distinct _ _ _
              (positions_distinct self body bodyCounts bodyBounded bodyDistinct right bounded.2 distinct.2 .whole [child])
          · exact .nil
  | ap functions arguments =>
      rw [positions.eq_def]
      apply sorted_distinct
      cases view with
      | whole =>
          dsimp only
          split
          · rename_i function argument
            exact product_distinct _ _ _ _
              (positions_distinct self body bodyCounts bodyBounded bodyDistinct functions bounded.1 distinct.1 .whole [function])
              (positions_distinct self body bodyCounts bodyBounded bodyDistinct arguments bounded.2 distinct.2 .whole [argument])
              (positions_bound self body bodyCounts bodyBounded functions bounded.1 .whole [function])
              (positions_bound self body bodyCounts bodyBounded arguments bounded.2 .whole [argument])
          · exact .nil
      | spine | labelled =>
          dsimp only
          split
          · exact .nil
          · rename_i argument found
            exact product_distinct _ _ _ _
              (positions_distinct self body bodyCounts bodyBounded bodyDistinct functions bounded.1 distinct.1 .spine wanted.dropLast)
              (positions_distinct self body bodyCounts bodyBounded bodyDistinct arguments bounded.2 distinct.2 .whole [argument])
              (positions_bound self body bodyCounts bodyBounded functions bounded.1 .spine wanted.dropLast)
              (positions_bound self body bodyCounts bodyBounded arguments bounded.2 .whole [argument])
  | label symbol inner =>
      rw [positions.eq_def]
      dsimp only
      split
      · rename_i found children
        split
        · exact pay_distinct _
            (positions_distinct self body bodyCounts bodyBounded bodyDistinct inner bounded distinct .labelled children)
        · exact .nil
      · exact .nil
termination_by (forestHeight wanted, depth recipe)
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [depth, forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  all_goals first
    | omega
    | have h := dropLast_height wanted; simp only [forestHeight] at h; omega
    | have h := last_height _ _ (by assumption); simp only [forestHeight] at h; omega

/-- Finite plan conversion cannot identify two distinct original callback ranks. -/
theorem converted_distinct (plan : SourcePlanPositions.Plan) (rows : List (Nat × Bool))
    (distinct : rows.Pairwise (fun a b => a.1 ≠ b.1)) :
    Distinct (SourcePlanPositions.convert plan rows) := by
  rw [Distinct, SourcePlanPositions.convert, List.pairwise_filterMap]
  apply distinct.imp
  intro a b different first firstFound second secondFound same
  obtain ⟨p, pf, ps⟩ := Option.map_eq_some_iff.mp firstFound
  obtain ⟨q, qf, qs⟩ := Option.map_eq_some_iff.mp secondFound
  subst first
  subst second
  have positionSame : p = q := same
  subst q
  have firstReplay := SourcePlanPositions.position_replay plan a.1 p pf
  have secondReplay := SourcePlanPositions.position_replay plan b.1 p qf
  exact different (Option.some.inj (firstReplay.symm.trans secondReplay))

/-- The actual static producer discharges the finite position-distinctness premise. -/
theorem static_terms_distinct [DecidableEq Symbol] (source : StaticCandidateRanks.Source Symbol)
    (plan : SourcePlanPositions.Plan) (view : View) (wanted : List (EngineTerm Symbol)) :
    Distinct ((staticTerms source plan).positions view wanted) := by
  have original : (StaticCheckedRanks.ranks source view wanted).Pairwise (fun a b => a.1 ≠ b.1) := by
    apply List.pairwise_map.mp
    exact (StaticRankQueryExact.callbacks_valid source view wanted).1.imp (fun smaller => Nat.ne_of_lt smaller)
  exact distinct_perm _ _ (List.mergeSort_perm _ _).symm (converted_distinct plan _ original)

end MicroCFTA.RecursiveCallbackDistinct
