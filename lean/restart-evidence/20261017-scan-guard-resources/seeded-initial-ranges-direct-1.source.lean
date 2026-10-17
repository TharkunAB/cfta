import MicroCFTA.SourceCurrentConstrainedCapSeededNumeric

/-!
# Seeded word ranges from initial numeric reservations

Initial selected support constructs the projection and tail returns.
Uniqueness identifies any supplied graph with those returns. The original
query reservation then derives its word checks. No reached range plan is
an input to this construction.
-/
namespace MicroCFTA.SourceCurrentSeededInitialRanges
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapSeededForecast (Reserved SeededReserved projectionProfile foldProfile)
open SourceCurrentAllocatedSeededQuery (Operand Fold FoldRanges SeededRanges)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem cons_ranges {values : List (Value Symbol Guard)} {seed path : List Int} {paths : List (List Int)}
    {before : Checked (bits + 2)}
    (tail : ∀ value middle, Operand path values before value middle → FoldRanges values (paths ++ [seed]) middle)
    (native : ∀ value middle rest later, Operand path values before value middle →
      Fold values (paths ++ [seed]) middle rest later →
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain value rest)) later) :
    FoldRanges values ((path :: paths) ++ [seed]) before := by
  cases paths <;> exact .cons tail native

/-- Initial support and reservations derive all word ranges in the original seeded fold. -/
theorem fold_ranges (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked (bits + 2)) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ seed :: paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ seed :: paths, path ≠ [])
    (reserved : Reserved bits values.length seed paths profile)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    FoldRanges values (paths ++ [seed]) before := by
  induction paths generalizing inventory before profile memos with
  | nil => exact .one
  | cons path paths ih =>
      obtain ⟨head, middle, middleMemos, first, firstReads, middleFrame, middleFits, firstEffects,
        _firstExtension, headAvailable, headClosed, firstGlobals, _firstDone⟩ :=
        SourceCurrentConstrainedCapSeededProjection.complete formulas solver inventory unconstrained anchor anchorSemantic anchorReady
          path values before profile frame fits available growth (supported path (by simp)) memos valid
      have nextValues : Values middle.native.machine.heap values :=
        fun value member => firstEffects.keeps.available value (available value member)
      have nextGrowth := grows_trans growth firstEffects.keeps.growth
      have nextSupport : ∀ value ∈ seed :: paths, PathSupport unconstrained anchor value values := by
        intro value member
        exact supported value (by simp only [List.mem_cons] at member ⊢; exact member.elim Or.inl (fun found => Or.inr (Or.inr found)))
      have nextProper : ∀ value ∈ seed :: paths, value ≠ [] := by
        intro value member
        exact proper value (by simp only [List.mem_cons] at member ⊢; exact member.elim Or.inl (fun found => Or.inr (Or.inr found)))
      have tailRanges := ih inventory middle (projectionProfile path values.length profile) middleFrame middleFits
        nextValues nextGrowth nextSupport nextProper reserved.1 middleMemos firstGlobals.valid
      obtain ⟨tail, later, next, _final, rest, _reads, receipt, laterFits, _included, _done⟩ :=
        SourceCurrentConstrainedCapSeededNumeric.fold_complete formulas solver inventory unconstrained anchor anchorSemantic anchorReady
          values seed paths middle (projectionProfile path values.length profile) middleFrame middleFits
          nextValues nextGrowth nextSupport nextProper reserved.1 middleMemos firstGlobals.valid
      apply cons_ranges
      · intro other after actual
        obtain ⟨rfl, rfl⟩ := first.unique actual
        exact tailRanges
      · intro other after result final actual actualRest
        obtain ⟨rfl, rfl⟩ := first.unique actual
        obtain ⟨rfl, rfl⟩ := rest.unique actualRest
        have room := laterFits.room reserved.2
        have resident := receipt.effects.keeps.available head headAvailable
        have facts := receipt.frame.ready.good.native.machine.1
        exact (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits later receipt.frame.ready.good
          receipt.frame.ready.semantic head tail
          (SourceRecursiveIntersectionOriginalOutput.closed_original head _ facts.coherent resident headClosed)
          (SourceRecursiveIntersectionOriginalOutput.closed_original tail _ facts.coherent receipt.available receipt.closed)
          resident receipt.available room.1 room.2.1 room.2.2).1

/-- Initial first-seeded support supplies the complete old range interface internally. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ [])
    (reserved : SeededReserved bits values.length paths profile)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    SeededRanges values paths before := by
  cases paths with
  | nil => trivial
  | cons seed rest => exact fold_ranges formulas solver inventory unconstrained anchor anchorSemantic anchorReady
      values seed rest before profile frame fits available growth supported proper reserved memos valid

end MicroCFTA.SourceCurrentSeededInitialRanges
