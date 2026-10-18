import MicroCFTA.SourceCurrentGeneratedGrowth
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
namespace MicroCFTA.GeneratedGrowthKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private theorem source_effect (term : Syntax Nat Bool) (names : List Reference)
    (before : State Nat Bool) (ready : Ready before)
    (available : InternedNestedProvenance.Values before (names.map Value.reference)) :
    build term (names.map Value.reference) before =
      .done (value (build term (names.map Value.reference) before)) (build term (names.map Value.reference) before).state ∧
      Keeps before (build term (names.map Value.reference) before).state ∧
      Available (build term (names.map Value.reference) before).state (value (build term (names.map Value.reference) before)) := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic _ available
  obtain ⟨result,after,called⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete term names before context ready.semantic.2 ready.covered
  have checked := InternedFreshOrdinaryFacts.build_verified term _ before ready.semantic.1.normal.facts available
  have kept : Keeps before after := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · simpa only [called,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source term _ before ready.semantic available
    · exact InternedFreshOrdinaryCoverage.build_covered term _ before ready.semantic.1.normal.facts.coherent.valid ready.covered result after called
    · simpa only [called,Outcome.state] using (InternedOpenDepthExecution.build_depth term _ before context ready.semantic.2 ready.depth).heap
    · simpa only [called,Outcome.state] using checked.growth
    · simpa only [called,Outcome.state] using checked.history
  rw [called]
  exact ⟨rfl,kept,checked.result result after called⟩

private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol true []]
private def built := build (leaf 0) [] empty
private def old := value built
private def before := built.state
private def extra := build (leaf 1) [] before
private def later := extra.state
private def q : Reference := .uninterned 1
private def r : Reference := .uninterned 2
private def firstNames : Unit → Reference := fun _ => q
private def secondNames : Unit → Reference := fun _ => r
private def firstMap : Environment Nat Bool := fun name => if name = q then some old else none
private def secondMap : Environment Nat Bool := fun name => if name = r then some old else none
private def symbols : List (Sum (Value Nat Bool) Unit) := [.inr (),.inl old]
private theorem actual : build (leaf 0) [] empty = .done old before := by cbv
private theorem ready : Ready before := SourceEqualityRequiredCache.constructed (leaf 0) old before actual
private theorem available : Available before old :=
  (InternedFreshOrdinaryFacts.build_verified (leaf 0) [] empty InternedNestedFacts.empty_facts
    (by intro supplied impossible; cases impossible)).result old before actual
private theorem effect : build (leaf 1) [] before = .done (value extra) later ∧ Keeps before later ∧ Available later (value extra) :=
  source_effect (leaf 1) [] before ready (by intro supplied impossible; cases impossible)
private theorem slots : Inputs before firstMap secondMap [.reference q,old] [.reference r,old] :=
  .reference (by change Generated before old old; exact .refl _) (by change Generated before old old; exact .refl _)
    (.fixed old (by
      intro name impossible
      have free : old.free = [] := by cbv
      rw [free] at impossible
      cases impossible) (.nil _ _))
private theorem generated : Generated before old old := by
  have base : Context before [old] :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context before ready.semantic [old]
      (by intro supplied member; obtain rfl := List.mem_singleton.mp member; exact available),ready.semantic.2⟩
  have qa : Available before (.reference q) := reference_available _ _ (InternedFreshProbeKeys.sentinel_references_issued _ 1).2
  have ra : Available before (.reference r) := reference_available _ _ (InternedFreshProbeKeys.sentinel_references_issued _ 2).2
  have aliases : Aliases (.var 0) symbols firstNames secondNames := by
    intro a ha b hb
    simp only [Scope,SourceCurrentNativeNormalizationInputs.support,InternedFreeNameSemantics.evaluate,
      symbols,List.map_cons,List.map_nil,List.getElem?_cons_zero,Option.getD_some,
      SourceCurrentNativeNormalizationInputs.inputNames,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [firstNames,secondNames,q,r]
  have tests : ∀ label ∈ Scope (.var 0) symbols,
      Sum.elim id firstNames label = q ↔ Sum.elim id secondNames label = r := by
    intro label member
    simp only [Scope,SourceCurrentNativeNormalizationInputs.support,InternedFreeNameSemantics.evaluate,
      symbols,List.map_cons,List.map_nil,List.getElem?_cons_zero,Option.getD_some,
      SourceCurrentNativeNormalizationInputs.inputNames,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp [firstNames,secondNames,q,r]
  have firstReplacements : Replacements before firstMap := by
    intro name output found
    dsimp only [firstMap] at found
    split at found
    · cases found; exact available
    · cases found
  have secondReplacements : Replacements before secondMap := by
    intro name output found
    dsimp only [secondMap] at found
    split at found
    · cases found; exact available
    · cases found
  exact .filtered (.var 0) symbols firstNames secondNames q r firstMap secondMap
    before before before before before before (.reference q) (.reference r) (.reference q) (.reference r) old old
    ready (base.local q qa) (base.local r ra) aliases tests slots firstReplacements secondReplacements qa ra
    (by cbv) (by cbv) rfl rfl (grows_refl _) (grows_refl _) (grows_refl _) (grows_refl _)
    (by cbv) (by cbv) rfl rfl (by cbv) (by cbv)
private theorem checked_witness :
    build (leaf 0) [] empty = .done old before ∧ Ready before ∧
    build (leaf 1) [] before = .done (value extra) later ∧ Keeps before later ∧
    before.nodes.next < later.nodes.next ∧
    Generated before old old ∧ Generated later old old ∧
    Inputs later firstMap secondMap [.reference q,old] [.reference r,old] := by
  exact ⟨actual,ready,effect.1,effect.2.1,by cbv,generated,
    SourceCurrentGeneratedGrowth.generated generated effect.2.1,
    SourceCurrentGeneratedGrowth.inputs slots effect.2.1⟩

/-- A source-built filtered generator and both lexical slot kinds survive a real later source allocation. -/
theorem actual_allocation :
    build (leaf 0) [] empty = .done old before ∧ Ready before ∧
    build (leaf 1) [] before = .done (value extra) later ∧ Keeps before later ∧
    before.nodes.next < later.nodes.next ∧
    Generated before old old ∧ Generated later old old ∧
    Inputs later firstMap secondMap [.reference q,old] [.reference r,old] := checked_witness
end MicroCFTA.GeneratedGrowthKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

#check @MicroCFTA.GeneratedGrowthKernels.actual_allocation
#print MicroCFTA.GeneratedGrowthKernels.actual_allocation
#print axioms MicroCFTA.GeneratedGrowthKernels.actual_allocation
