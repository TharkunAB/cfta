import MicroCFTA.SourceRecursiveIntersectionMassInputBounds
import MicroCFTA.IntersectNumericRank
import MicroCFTA.IntersectNumericFuel

/-!
# Computed initial fuel from source counters and payload mass

Mass bounds the full original source family. A finite tagged input inventory
and bounded termination tuple give a computed semantic fuel ceiling. The
proof constructs stable execution without selecting a completed trace length.
-/
namespace MicroCFTA.SourceRecursiveIntersectionComputedFuel
open Cache Language Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
variable {Symbol Guard : Type}

/-- Source node count and one payload mass bound give a numeric semantic fuel ceiling. -/
def ceiling (nodes bound : Nat) : Nat :=
  IntersectNumericRank.ceiling ((1 + 4 * nodes) * (1 + 4 * nodes)) bound

/-- Larger source counters and payload mass retain the computed fuel ceiling. -/
theorem ceiling_mono {firstNodes lastNodes firstBound lastBound : Nat}
    (nodes : firstNodes ≤ lastNodes) (mass : firstBound ≤ lastBound) :
    ceiling firstNodes firstBound ≤ ceiling lastNodes lastBound := by
  have carrier : 1 + 4 * firstNodes ≤ 1 + 4 * lastNodes := by omega
  have pairs := Nat.mul_le_mul carrier carrier
  exact Nat.mul_le_mul_right 2
    (Nat.mul_le_mul (Nat.mul_le_mul (by omega : 2 * firstBound + 1 ≤ 2 * lastBound + 1)
      (Nat.add_le_add_right pairs 1)) (by omega : 2 * firstBound + 2 ≤ 2 * lastBound + 2))

variable [DecidableEq Symbol]

/-- All closed original source inputs execute at the computed numeric ceiling. -/
theorem schedule_numeric (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (leftRoot rightRoot : Input)
    (leftOriginal : OriginalInput source leftRoot) (rightOriginal : OriginalInput source rightRoot)
    (leftClosed : closed (view source holds) leftRoot = true)
    (rightClosed : closed (view source holds) rightRoot = true)
    {bound : Nat} (stored : InternedValueMassHeap.Stored bound source) :
    ∃ result, ∀ fuel, ceiling source.nodes.next bound ≤ fuel →
      IntersectSchedule.execute (view source holds) fuel (.node {} leftRoot rightRoot) = .ok result := by
  let inputs := finiteInput source facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed
  let bounds := SourceRecursiveIntersectionMassInputBounds.mass_inputBounds source facts holds leftRoot rightRoot
    leftOriginal rightOriginal leftClosed rightClosed
  let roots : ClosedRoots (view source holds) inputs :=
    ⟨leftRoot, rightRoot, .inl .root, .inr .root, leftClosed, rightClosed⟩
  have sizes : ∀ input, bounds.size input ≤ bound :=
    SourceRecursiveIntersectionMassInputBounds.mass_stored source facts stored
  have weights : ∀ input, bounds.localWeight.value input ≤ bound :=
    SourceRecursiveIntersectionMassInputBounds.local_stored source facts stored
  obtain ⟨result, success⟩ := IntersectNumericFuel.call_numeric (view source holds) inputs (free_correct source facts holds)
    bounds (IntersectNumericRank.rank bounds bound)
    (fun before after parent child less _ _ => IntersectNumericRank.root_decrease bounds bound weights before after parent child less)
    (fun before after parent child same _ _ actual => IntersectNumericRank.local_decrease bounds bound weights before after parent child same actual)
    roots (.node {} leftRoot rightRoot) (roots_ready _ _ roots)
  have rankBound := IntersectNumericRank.rank_bound bounds bound sizes weights roots (.node {} leftRoot rightRoot)
  have count : bounds.pairs.length = (1 + 4 * source.nodes.next) * (1 + 4 * source.nodes.next) :=
    SourceRecursiveIntersectionMassInputBounds.pairs_length source
  have enough : IntersectNumericRank.rank bounds bound roots (.node {} leftRoot rightRoot) + 1 ≤ ceiling source.nodes.next bound := by
    unfold ceiling
    rw [← count]
    omega
  exact ⟨result, fun fuel room => success fuel (Nat.le_trans enough room)⟩

/-- Actual closed original operands derive semantic execution at the initial numeric source ceiling. -/
theorem initial_numeric (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    {bound : Nat} (stored : InternedValueMassHeap.Stored bound source) :
    ∃ result, ∀ fuel, ceiling source.nodes.next bound ≤ fuel →
      IntersectSchedule.execute (view source holds) fuel
        (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) = .ok result := by
  have first : closed (view source holds) (inputOf left) = true := by
    rw [closed_readback source facts holds left leftOriginal leftAvailable, leftClosed]
    rfl
  have second : closed (view source holds) (inputOf right) = true := by
    rw [closed_readback source facts holds right rightOriginal rightAvailable, rightClosed]
    rfl
  exact schedule_numeric source facts holds (inputOf left) (inputOf right)
    ⟨left, leftOriginal, leftAvailable, leftOriginal.codec left⟩
    ⟨right, rightOriginal, rightAvailable, rightOriginal.codec right⟩ first second stored

/-- The least semantic fuel fits the computed bound from the initial source. -/
theorem initial_requiredFuel_le (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    {bound : Nat} (stored : InternedValueMassHeap.Stored bound source)
    (complete : Completes (view source holds) (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)) :
    requiredFuel (view source holds) (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete ≤
      ceiling source.nodes.next bound := by
  obtain ⟨result, success⟩ := initial_numeric source facts holds left right leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed stored
  exact requiredFuel_le _ _ complete _ result (success _ (Nat.le_refl _))

end MicroCFTA.SourceRecursiveIntersectionComputedFuel
