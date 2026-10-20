import MicroCFTA.SourceCurrentNativeMuGrowthHistory

/-!
# The actual raw callback suffix to Mu publication

The raw source return passes through its actual self-reference filter.
Publication then retains every earlier full cell and issued reference.
-/
namespace MicroCFTA.SourceCurrentNativePublicationRawSuffix
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
variable {Symbol Guard : Type}

/-- The actual raw build and filter derive physical and issued growth to the same publication return. -/
theorem callback_suffix [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (raw : Value Symbol Guard) (rawAfter : State Symbol Guard)
    (context : Context event.allocated
      (.reference (.interned event.entry.identity) :: event.environment))
    (built : InternedFreshOrdinaryConstruction.build event.expression
      (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw rawAfter)
    (filtered : run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter =
      (event.body,event.afterBody)) :
    Grows rawAfter event.after ∧ Extends rawAfter.nodes.issued event.after.nodes.issued := by
  have returned := context.build event.expression
  rw [built,Outcome.state] at returned
  have valid := returned.base.normal.facts.coherent.valid
  have filterGrowth := (run_correct (withoutSelfReference (.interned event.entry.identity) raw) rawAfter valid).2
  have filterIssued := run_issued_extends (withoutSelfReference (.interned event.entry.identity) raw) rawAfter valid
  rw [filtered] at filterGrowth filterIssued
  have published := SourceCurrentNativeMuGrowthHistory.publication_growth event
  have publishedIssued : Extends event.afterBody.nodes.issued event.after.nodes.issued := by
    change Extends event.afterBody.nodes.issued event.afterBody.nodes.issued
    exact extends_refl _
  exact ⟨grows_trans filterGrowth published,extends_trans filterIssued publishedIssued⟩

end MicroCFTA.SourceCurrentNativePublicationRawSuffix
