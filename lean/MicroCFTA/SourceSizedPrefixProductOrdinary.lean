import MicroCFTA.SourceRankedRowsOrdinaryConstruction
import MicroCFTA.SourceSizedPrefixProductRank

/-!
# Ordinary native values from generated size-product rows

The input is the original rows, minimum table, numeric filter and size bound.
The synthetic root uses its generated row list without an extra constructor.
The native construction is ranked-DAG unfolding, not the source SCC/memo import.
Integer/minimum-table and host constructor correspondence remain separate.
-/
namespace MicroCFTA.SourceSizedPrefixProductOrdinary
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceSizedDecided (Row)
variable {Q Symbol Guard : Type}

/-- Any generated nonempty row class has positive original rank. -/
theorem rows_positive (original : Q → List (Row Q Symbol Guard))
    (minimum : Q → Option Nat) (equalSizes : Guard → List Nat → Bool)
    (root : Q) (bound : Int) (current : Option (Q × Nat))
    (row : Row (Option (Q × Nat)) Symbol Guard)
    (member : row ∈ SourceSizedPrefixProductRank.rows original minimum equalSizes root bound current) :
    0 < SourceSizedPrefixProductRank.rank bound current := by
  cases current with
  | none => simp [SourceSizedPrefixProductRank.rank]
  | some pair =>
      rcases pair with ⟨state, budget⟩
      cases budget with
      | zero => simp [SourceSizedPrefixProductRank.rows, SourceSizedPrefixProductRank.rowOf] at member
      | succ budget => simp [SourceSizedPrefixProductRank.rank]

/-- Unfold the complete generated root row sequence at its original rank. -/
def expression (original : Q → List (Row Q Symbol Guard))
    (minimum : Q → Option Nat) (equalSizes : Guard → List Nat → Bool)
    (root : Q) (bound : Int) : Syntax Symbol Guard :=
  SourceRankedRowsOrdinaryConstruction.expression
    (SourceSizedPrefixProductRank.rows original minimum equalSizes root bound)
    (bound.toNat + 2) none

/-- Actual fresh construction derives finite ordinary structure from original product inputs. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)]
    (original : Q → List (Row Q Symbol Guard))
    (minimum : Q → Option Nat) (equalSizes : Guard → List Nat → Bool)
    (root : Q) (bound : Int) :
    ∃ (value : Value Symbol Guard) (heap : State Symbol Guard),
      InternedFreshOrdinaryConstruction.build (expression original minimum equalSizes root bound) [] empty = .done value heap ∧
      InternedNestedFacts.Facts heap ∧ Available heap value ∧ value.free = [] ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧
      MergedOrdinaryHeight.height value ≤ bound.toNat + 1 := by
  exact SourceRankedRowsOrdinaryConstruction.closed
    (SourceSizedPrefixProductRank.rows original minimum equalSizes root bound)
    (SourceSizedPrefixProductRank.rank bound)
    (rows_positive original minimum equalSizes root bound)
    (SourceSizedPrefixProductRank.rows_rank original minimum equalSizes root bound) none

end MicroCFTA.SourceSizedPrefixProductOrdinary
