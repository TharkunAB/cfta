import MicroCFTA.SourceSizedGroupedPreparedRank
import MicroCFTA.SourceSizedGroupedPublicQueries

/-!
# Signed inverses for prepared grouped source queries

The source signed rank maps the bottom-up result to Integer size and rank.
The selector retains the literal fromTable rank guard. Its proved zero
count at nonpositive sizes supplies rejection at those sizes.

Actual validation, scoped unambiguity, and successful preparation derive
both signed inverse directions. The rank does not search class lists.
These laws concern constructed source field observations. Native signed
sparse lookup, lazy sharing, finite map storage, and cached execution remain
separate. No size guard or complete public Exact contract is added here.
-/
namespace MicroCFTA.SourceSizedGroupedSignedRank
open Language RecursiveSize SizedRank SourceSizedDecided SourceSizedFiniteKeys

variable {State Symbol Formula : Type}
  [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Map the actual bottom-up source rank to its unbounded Integer components. -/
def rankSigned (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) : Option (Int × Int) :=
  (SourceSizedGroupedPreparedRank.rankAt original root output success key term).map
    (fun position => (Int.ofNat position.size, Int.ofNat position.rank))

/-- Signed rank existence is exactly acceptance by the prepared guarded graph. -/
theorem rankSigned_exists_iff (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) :
    (∃ signed, rankSigned original root output success key term = some signed) ↔
      Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) key term := by
  constructor
  · rintro ⟨signed, found⟩
    obtain ⟨position, ranked, _⟩ := Option.map_eq_some_iff.mp found
    exact (SourceSizedGroupedPreparedRank.rankAt_exists_iff original root output success key term).mp ⟨position, ranked⟩
  · intro accepted
    obtain ⟨position, ranked⟩ :=
      (SourceSizedGroupedPreparedRank.rankAt_exists_iff original root output success key term).mpr accepted
    exact ⟨(Int.ofNat position.size, Int.ofNat position.rank), by simp [rankSigned, ranked]⟩

/-- Successful signed ranks have the actual positive node size and an in-class nonnegative rank. -/
theorem rankSigned_bounds (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) (size rank : Int)
    (found : rankSigned original root output success key term = some (size, rank)) :
    (nodeSize term : Int) = size ∧ 0 < size ∧ 0 ≤ rank ∧
      rank < (SourceSizedGroupedPublicQueries.countAt original root output success key size : Int) := by
  obtain ⟨position, ranked, same⟩ := Option.map_eq_some_iff.mp found
  have sizeEq : (position.size : Int) = size := congrArg Prod.fst same
  have rankEq : (position.rank : Int) = rank := congrArg Prod.snd same
  have sized := SourceSizedGroupedPreparedRank.rankAt_size original root output success key term position ranked
  have replay := SourceSizedGroupedPreparedRank.rankAt_replay original root output success key term position ranked
  have within := (List.getElem?_eq_some_iff.mp replay).1
  have counts := SourceSizedGroupedPublicQueries.countAt_eq original root output success key (position.size : Int)
  simp only [Int.toNat_natCast] at counts
  rw [← sizeEq, ← rankEq, counts]
  have positive := nodeSize_pos term
  omega

/-- A successful public signed selector has a positive size and passes its literal rank guard. -/
theorem unrank_bounds (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (term : Term Symbol) (size rank : Int)
    (selected : SourceSizedGroupedPublicQueries.unrankAt original root output success key size rank = some term) :
    0 < size ∧ 0 ≤ rank ∧
      rank < (SourceSizedGroupedPublicQueries.countAt original root output success key size : Int) := by
  have valid : ¬(rank < 0 ∨ (SourceSizedGroupedPublicQueries.countAt original root output success key size : Int) ≤ rank) := by
    intro invalid
    have rejected := (SourceSizedGroupedPublicQueries.unrankAt_none_iff
      original root output success key size rank).mpr invalid
    rw [rejected] at selected
    cases selected
  have positive : 0 < size := by
    by_cases nonpositive : size ≤ 0
    · have rejected := SourceSizedGroupedPublicQueries.unrankAt_nonpositive
        original root output success key size rank nonpositive
      rw [rejected] at selected
      cases selected
    · omega
  exact ⟨positive, by omega, by omega⟩

/-- The actual scoped branch gives both inverse directions for all signed source queries. -/
theorem rankSigned_unrank_iff
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (key : List State) (term : Term Symbol) (size rank : Int) :
    rankSigned (SourceSizedScopedTrimInventory.trimmedTable table root) root output success key term =
        some (size, rank) ↔
      SourceSizedGroupedPublicQueries.unrankAt
        (SourceSizedScopedTrimInventory.trimmedTable table root) root output success key size rank = some term := by
  constructor
  · intro found
    obtain ⟨position, ranked, same⟩ := Option.map_eq_some_iff.mp found
    have sizeEq : (position.size : Int) = size := congrArg Prod.fst same
    have rankEq : (position.rank : Int) = rank := congrArg Prod.snd same
    have selected := (SourceSizedGroupedPreparedRank.rankAt_select_iff table root validated passed
      output success key term position.size position.rank).mp ranked
    rw [SourceSizedGroupedPreparedIndex.selectAt_eq] at selected
    rw [← sizeEq, ← rankEq, SourceSizedGroupedPublicQueries.unrankAt_nat]
    exact selected
  · intro selected
    obtain ⟨sizePositive, rankNonnegative, _⟩ := unrank_bounds
      (SourceSizedScopedTrimInventory.trimmedTable table root) root output success key term size rank selected
    have sizeCast : (size.toNat : Int) = size := Int.toNat_of_nonneg (by omega)
    have rankCast : (rank.toNat : Int) = rank := Int.toNat_of_nonneg rankNonnegative
    have naturalSelected : SourceSizedGroupedPreparedIndex.selectAt
        (SourceSizedScopedTrimInventory.trimmedTable table root) root output success
        size.toNat rank.toNat key = some term := by
      rw [SourceSizedGroupedPreparedIndex.selectAt_eq]
      rw [SourceSizedGroupedPublicQueries.unrankAt_eq] at selected
      simpa only [rankNonnegative, ite_true] using selected
    have ranked := (SourceSizedGroupedPreparedRank.rankAt_select_iff table root validated passed
      output success key term size.toNat rank.toNat).mpr naturalSelected
    simp only [rankSigned, ranked, Option.map_some]
    apply congrArg some
    apply Prod.ext
    · exact sizeCast
    · exact rankCast

/-- The signed inverse specializes to every natural request size and rank. -/
theorem rankSigned_unrank_nat_iff
    (table : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (key : List State) (term : Term Symbol) (size rank : Nat) :
    rankSigned (SourceSizedScopedTrimInventory.trimmedTable table root) root output success key term =
        some ((size : Int), (rank : Int)) ↔
      SourceSizedGroupedPublicQueries.unrankAt
        (SourceSizedScopedTrimInventory.trimmedTable table root) root output success key (size : Int) (rank : Int) = some term :=
  rankSigned_unrank_iff table root validated passed output success key term (size : Int) (rank : Int)

open SourceGuards SourceObservations SourceSymbolicIndex

/-- Original root signed rank existence uses the current raw constraint language. -/
theorem root_rankSigned_iff [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (table : Table State (Label Formula) (Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (output : SourceSizedConjunctionWorklist.Stored State (Label Formula))
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (term : Term (Label Formula)) :
    (∃ signed, rankSigned (SourceSizedScopedTrimInventory.trimmedTable table root)
      root output success [root] term = some signed) ↔
      Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver table) root term :=
  (rankSigned_exists_iff (SourceSizedScopedTrimInventory.trimmedTable table root)
    root output success [root] term).trans
      (SourceSizedGroupedCurrent.prepared_root_language formulas solver table root validated output success term)

end MicroCFTA.SourceSizedGroupedSignedRank
