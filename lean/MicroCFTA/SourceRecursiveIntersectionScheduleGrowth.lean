import MicroCFTA.IntersectViewAgreement
import MicroCFTA.SourceRecursiveIntersectionInputGrowth

/-!
# Actual heap growth retains the complete reference schedule

Stored records and issued-key history retain all reads on original inputs.
The reference schedule therefore has the same bounded outcome after actual
constructor growth. Its finite complete result also remains unchanged.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Language Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open IntersectSchedule

/-- Actual cache growth gives complete view agreement on available original payloads. -/
theorem growthAgreement (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool) :
    ViewAgreement (view before holds) (view after holds) (OriginalInput before) where
  free := fun input original => free_grows before after beforeFacts afterFacts growth history holds input original
  copy := fun input original => copy_grows before after beforeFacts afterFacts growth history holds input original
  body := fun name original => body_grows before after beforeFacts afterFacts growth history holds name original
  rows := fun name original => rows_grows before after beforeFacts afterFacts growth history holds name original
  members := fun name original => members_grows before after beforeFacts afterFacts growth history holds name original
  body_valid := fun name original => original.body before beforeFacts holds name
  child_valid := fun name original row present child member => original.child before beforeFacts holds name row present child member
  member_valid := fun name original child member => original.member before beforeFacts holds name child member

/-- Every bounded original-input schedule outcome is retained by actual cache and history growth. -/
theorem run_grows [DecidableEq Symbol] (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool)
    (fuel : Nat) (domain : IntersectSchedule.Domain) (known : DomainInputs (OriginalInput before) domain)
    (left right : Input) (leftOriginal : OriginalInput before left) (rightOriginal : OriginalInput before right) :
    IntersectSchedule.run (view after holds) fuel domain left right =
      IntersectSchedule.run (view before holds) fuel domain left right :=
  run_view_agreement (view before holds) (view after holds) (OriginalInput before)
    (growthAgreement before after beforeFacts afterFacts growth history holds) fuel domain known left right leftOriginal rightOriginal

/-- Ordered original row children retain the exact edge-worker outcome after actual cache growth. -/
theorem edge_grows [DecidableEq Symbol] (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool)
    (fuel : Nat) (domain : IntersectSchedule.Domain) (known : DomainInputs (OriginalInput before) domain)
    (left right : Row Symbol)
    (leftOriginal : ∀ child ∈ left.children, OriginalInput before child)
    (rightOriginal : ∀ child ∈ right.children, OriginalInput before child) :
    IntersectSchedule.edge (view after holds) fuel domain left right =
      IntersectSchedule.edge (view before holds) fuel domain left right :=
  (view_agreement_workers (view before holds) (view after holds) (OriginalInput before)
    (growthAgreement before after beforeFacts afterFacts growth history holds) fuel).2 domain known left right leftOriginal rightOriginal

/-- Actual closed original roots have one finite exact schedule result in every later valid heap. -/
theorem source_schedule_total_grows [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state left) (rightAvailable : Available state right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound result,
      (∀ after, Facts after → Grows state after → Extends state.nodes.issued after.nodes.issued →
        ∀ fuel, bound ≤ fuel → IntersectSchedule.run (view after holds) fuel {} (inputOf left) (inputOf right) = .ok result) ∧
      ∀ ambient term, meaning ambient result term ↔
        meaning ambient (shape holds left) term ∧ meaning ambient (shape holds right) term := by
  obtain ⟨bound, result, completed, exactResult⟩ := source_schedule_total state facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  refine ⟨bound, result, ?_, exactResult⟩
  intro after afterFacts growth history fuel enough
  rw [run_grows state after facts afterFacts growth history holds fuel {} (DomainInputs.empty _) _ _
    ⟨left, leftOriginal, leftAvailable, leftOriginal.codec left⟩ ⟨right, rightOriginal, rightAvailable, rightOriginal.codec right⟩]
  exact completed fuel enough

end MicroCFTA.SourceRecursiveIntersectionInputView
