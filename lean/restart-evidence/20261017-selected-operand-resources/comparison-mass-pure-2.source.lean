import MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
import MicroCFTA.SourceMergedComparisonEffects

/-!
# Numeric resources for actual repaired comparisons

The supplied comparison fuel and initial causal payload bound determine a
numeric envelope. Actual reads and recursive calls derive every local bound.
The theorem covers successful closed recursive comparisons. It does not
derive an initial sufficient comparison fuel.
-/
namespace MicroCFTA.SourceMergedComparisonMass
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (Effect bind_done read_graph)
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
variable {Symbol Guard : Type}

/-- One envelope bounds payloads and both increments from the original heap. -/
structure Resources (bound : Nat) (before after : State Symbol Guard) : Prop where
  /-- Every complete returned payload fits the envelope. -/
  stored : Stored bound after
  /-- The literal node supply fits the original supply plus the envelope. -/
  nodes : after.nodes.next ≤ before.nodes.next + bound
  /-- The literal edge supply fits the same increment envelope. -/
  edges : after.edges.next ≤ before.edges.next + bound

/-- A causal initial store supplies the initial numeric envelope. -/
theorem Resources.refl (before : State Symbol Guard) (bound : Nat) (stored : Stored bound before) :
    Resources bound before before := ⟨stored, Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- A larger envelope retains the exact physical endpoints. -/
theorem Resources.mono {before after : State Symbol Guard} {first last : Nat}
    (known : Resources first before after) (enough : first ≤ last) : Resources last before after :=
  ⟨known.stored.mono enough, Nat.le_trans known.nodes (Nat.add_le_add_left enough _),
    Nat.le_trans known.edges (Nat.add_le_add_left enough _)⟩

/-- Numeric growth retains inequalities between initial bounds. -/
def Monotone (growth : Nat → Nat) : Prop := ∀ {first last : Nat}, first ≤ last → growth first ≤ growth last

/-- An ordered finite scan starts each action at its actual earlier bound. -/
def iterate (growth : Nat → Nat) : Nat → Nat → Nat
  | 0, bound => bound
  | count + 1, bound => iterate growth count (growth bound)

/-- Monotone actions retain ordered bounds through a fixed scan. -/
theorem iterate_mono {growth : Nat → Nat} (mono : Monotone growth) (count : Nat)
    {first last : Nat} (enough : first ≤ last) : iterate growth count first ≤ iterate growth count last := by
  induction count generalizing first last with
  | zero => exact enough
  | succ count ih => exact ih (mono enough)

/-- Inflationary actions retain the initial envelope. -/
theorem iterate_ge {growth : Nat → Nat} (ge : ∀ bound, bound ≤ growth bound) (count bound : Nat) :
    bound ≤ iterate growth count bound := by
  induction count generalizing bound with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (ge bound) (ih _)

/-- Additional actions retain each earlier envelope. -/
theorem iterate_count_mono {growth : Nat → Nat} (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    iterate growth first bound ≤ iterate growth last bound := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (iterate_mono mono last (ge bound))

/-- Pointwise larger monotone actions support the same number of calls. -/
theorem iterate_family_mono {first last : Nat → Nat} (mono : Monotone last)
    (enough : ∀ bound, first bound ≤ last bound) (count bound : Nat) :
    iterate first count bound ≤ iterate last count bound := by
  induction count generalizing bound with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (ih _) (iterate_mono mono count (enough bound))

/-- One repaired read includes its old prefix credit and actual constructor charges. -/
def readBound (fuel bound : Nat) : Nat := massAfter (fuel + 1) bound + bound + credit (fuel + 1) bound

/-- The actual reader can return at most this many rows. -/
def readWidth (fuel bound : Nat) : Nat := (fuel + 1) * massAfter (fuel + 1) bound

private theorem read_ge (fuel bound : Nat) : bound ≤ readBound fuel bound := by
  unfold readBound
  omega

private theorem read_mono (fuel : Nat) : Monotone (readBound fuel) := by
  intro first last enough
  exact Nat.add_le_add (Nat.add_le_add
    (SourceCurrentAllocatedRecursiveMassMonotone.massAfter_bound_mono _ enough) enough)
    (SourceCurrentAllocatedRecursiveMassMonotone.credit_bound_mono _ enough)

private theorem width_mono (fuel : Nat) : Monotone (readWidth fuel) := by
  intro first last enough
  exact Nat.mul_le_mul_left _ (SourceCurrentAllocatedRecursiveMassMonotone.massAfter_bound_mono _ enough)

private def childrenBound (growth : Nat → Nat) (bound : Nat) : Nat := iterate growth bound bound

private theorem children_ge {growth : Nat → Nat} (ge : ∀ bound, bound ≤ growth bound) (bound : Nat) :
    bound ≤ childrenBound growth bound := iterate_ge ge bound bound

private theorem children_mono {growth : Nat → Nat} (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) : Monotone (childrenBound growth) := by
  intro first last enough
  exact Nat.le_trans (iterate_count_mono mono ge enough first) (iterate_mono mono last enough)

private def rowBound (fuel : Nat) (growth : Nat → Nat) (bound : Nat) : Nat :=
  iterate (childrenBound growth) (readWidth fuel bound) (readBound fuel bound)

private theorem row_ge (fuel : Nat) {growth : Nat → Nat} (ge : ∀ bound, bound ≤ growth bound) (bound : Nat) :
    bound ≤ rowBound fuel growth bound := Nat.le_trans (read_ge fuel bound) (iterate_ge (children_ge ge) _ _)

private theorem row_mono (fuel : Nat) {growth : Nat → Nat} (mono : Monotone growth)
    (ge : ∀ bound, bound ≤ growth bound) : Monotone (rowBound fuel growth) := by
  intro first last enough
  exact Nat.le_trans (iterate_count_mono (children_mono mono ge) (children_ge ge) (width_mono fuel enough) _)
    (iterate_mono (children_mono mono ge) _ (read_mono fuel enough))

/-- Each recursive comparison level pays for its actual narrow and wide reads. -/
def comparisonBound : Nat → Nat → Nat
  | 0, bound => bound
  | fuel + 1, bound => iterate (rowBound (fuel + 1) (comparisonBound fuel))
      (readWidth (fuel + 1) bound) (readBound (fuel + 1) bound)

/-- The comparison envelope retains the initial store bound. -/
theorem comparisonBound_ge (fuel bound : Nat) : bound ≤ comparisonBound fuel bound := by
  induction fuel generalizing bound with
  | zero => exact Nat.le_refl _
  | succ fuel ih => exact Nat.le_trans (read_ge _ _) (iterate_ge (row_ge _ ih) _ _)

/-- A larger initial store supports the same comparison fuel. -/
theorem comparisonBound_mono (fuel : Nat) : Monotone (comparisonBound fuel) := by
  induction fuel with
  | zero => exact fun _ _ enough => enough
  | succ fuel ih =>
      intro first last enough
      exact Nat.le_trans (iterate_count_mono (row_mono _ ih (comparisonBound_ge fuel))
        (row_ge _ (comparisonBound_ge fuel)) (width_mono _ enough) _)
        (iterate_mono (row_mono _ ih (comparisonBound_ge fuel)) _ (read_mono _ enough))

variable [DecidableEq (EdgeKey Symbol Guard)]

end MicroCFTA.SourceMergedComparisonMass
