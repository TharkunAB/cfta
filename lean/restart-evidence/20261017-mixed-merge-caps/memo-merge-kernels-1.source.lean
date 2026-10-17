import MicroCFTA.SourceCurrentConstrainedCapMemoMerge
import MicroCFTA.SourceCurrentMemoMergeCompletion
import MicroCFTA.InternedFreshOrdinaryCosts

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.MixedMergeCapsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache SourceCurrentMemoMergeGraph
open SourceCurrentConstrainedCap (Cap)
namespace Caps
export SourceCurrentConstrainedCapMemoMerge (Stored cold call)
end Caps
namespace Local
export SourceCurrentConstrainedCapMemoMergeCode (Certificate)
end Local
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private def badPlan : InternedNestedConstruction.Syntax Nat Bool := .node [.mk 0 false []]

private def badValue : Value Nat Bool :=
  .node {identity := 0, key := .node [0]}
    [.mk {identity := 0, key := ⟨0, [], false⟩} []] 0 []

set_option cbv.maxSteps 100000000 in
private theorem bad_computed :
    (match InternedFreshOrdinaryConstruction.build badPlan [] InternedConstructorTemplates.empty with
    | .done value _ => value | .pending .. => .empty) = badValue := by cbv

/-- An actual constrained source gets its own cold Merge call and an exact warm replay. -/
theorem constructed_positive_cold_then_warm :
    ∃ before result after saved,
      InternedFreshOrdinaryConstruction.build badPlan [] InternedConstructorTemplates.empty =
        .done badValue before ∧
      Cap (fun guard : Bool => guard = true) 1 badValue ∧
      ¬SourceEqualityAnnotationLanguage.Annotated (fun guard : Bool => guard = true) badValue ∧
      Call id true badValue before empty result after saved ∧
      Call id true badValue after saved result after saved ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧
      Caps.Stored (fun guard : Bool => guard = true) saved ∧
      Cap (fun guard : Bool => guard = true) 1 result ∧
      (∀ later final completed, Call id true badValue after saved later final completed →
        final = after ∧ completed = saved ∧ later = result) := by
  obtain ⟨value, before, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete badPlan
  have same : value = badValue := by simpa only [built] using bad_computed
  subst value
  have available := (InternedFreshOrdinaryFacts.closed_verified badPlan).result badValue before built
  have semantic := SourceEqualityRequiredSemanticCache.constructed badPlan badValue before built
  have costs : CostHeap before := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap badPlan
  have bounded : Cap (fun guard : Bool => guard = true) 1 badValue := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, EdgeValue.children, List.nil_append] at member
    cases member
  have nonhereditary : ¬SourceEqualityAnnotationLanguage.Annotated (fun guard : Bool => guard = true) badValue := by
    intro annotated
    cases annotated with
    | node _ _ _ _ guards _ =>
        have impossible := guards _ List.mem_cons_self
        cases impossible
  obtain ⟨result, after, saved, actual, _⟩ :=
    SourceCurrentMemoMergeCompletion.cold_complete id true badValue before semantic costs available
  obtain ⟨effect, physical, stored, returned⟩ := Caps.cold (fun guard : Bool => guard = true) rfl
    actual semantic costs available
  obtain ⟨entry, found, same⟩ := actual.present
  have warm : Call id true badValue after saved result after saved := by
    rw [same]
    exact .hit found
  have repeated := Caps.call (fun guard : Bool => guard = true) rfl warm effect.semantic effect.costs
    physical stored (effect.keeps.available badValue available)
  exact ⟨before, result, after, saved, built, bounded, nonhereditary, actual, warm,
    repeated.2.1, repeated.2.2.1, repeated.2.2.2.2 1 bounded,
    fun _ _ _ next => by simpa only [same] using next.hit_unchanged entry found⟩

/-- An actual reentrant body proves the candidate before it retains an earlier winner. -/
theorem actual_candidate_and_keep_first {Symbol Guard : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input candidate : Value Symbol Guard} {before after : State Symbol Guard}
    {current : Memo Symbol Guard} {entry : Entry Symbol Guard}
    (body : Run clear top (SourceCurrentMemoMergeGraph.body top input) before empty candidate after current)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (found : current input.referenceOf = some entry) :
    Local.Certificate valid input candidate ∧
      remember current input candidate = current ∧ winner current input candidate = entry ∧
      entry.original = input ∧ SourceCurrentMemoMergeEffects.Stored after current ∧
      Caps.Stored valid current ∧ Local.Certificate valid input entry.result := by
  obtain ⟨effect, physical, caps, candidateLaw⟩ :=
    SourceCurrentConstrainedCapMemoMerge.run valid topValid body _ semantic costs
      (SourceCurrentMemoMergeEffects.stored_empty before) (SourceCurrentConstrainedCapMemoMerge.stored_empty valid)
      (SourceCurrentConstrainedCapMemoMergeCode.body_certified valid clear top topValid input before semantic costs available)
  have completed := SourceCurrentConstrainedCapMemoMerge.winner_certificate effect.semantic
    (effect.keeps.available input available) physical caps candidateLaw
  have old := winner_existing current input candidate entry found
  exact ⟨candidateLaw, old.1, old.2, old.2 ▸ completed.1, physical, caps, old.2 ▸ completed.2.1⟩

#print axioms constructed_positive_cold_then_warm
#check @constructed_positive_cold_then_warm
#print axioms actual_candidate_and_keep_first
#check @actual_candidate_and_keep_first
end MicroCFTA.MixedMergeCapsKernels
