import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
import MicroCFTA.InternedNormalizationDepthExact

/-!
# Original child depths at actual source constructors

Completed source calls expose their literal child calls and constructor
states. Surviving node rows bound each original child. Union construction
bounds every original member, including members removed by normalization.
Dead node rows have no depth obligation.
-/
namespace MicroCFTA.SourceCurrentSourceChildDepth
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open SourceCurrentConstrainedCapSourceHistory (Context)

/-- Each child of an actual surviving source row has depth at most the raw node result's depth. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (context : Context before environment) (raw : Value Symbol Guard)
    (actual : build (.node expressions) environment before = .done raw after) :
    ∃ rows middle,
      buildEdges expressions environment before = .done rows middle ∧
      run (makeNode rows) middle = (raw, after) ∧ Context middle environment ∧
      ∀ row ∈ surviving rows, ∀ child ∈ row.children, child.depth ≤ raw.depth := by
  cases built : buildEdges expressions environment before with
  | pending key state => simp only [build, built, Outcome.bind] at actual; cases actual
  | done rows middle =>
      simp only [build, built, Outcome.bind, work, Outcome.done.injEq] at actual
      have made : run (makeNode rows) middle = (raw, after) := Prod.ext actual.1 actual.2
      have middleContext : Context middle environment := by
        simpa only [built, Outcome.state] using context.edges expressions
      have resident := (buildEdges_verified expressions environment before context.base.normal.facts
        context.base.inputs).result rows middle built
      have depth := InternedNormalizationDepthExact.makeNode_surviving_depth rows middle
        middleContext.base.normal.facts.coherent middleContext.base.normal.facts.linked resident
      rw [made] at depth
      refine ⟨rows, middle, rfl, made, middleContext, ?_⟩
      intro row member child selected
      rw [depth]
      exact (maximumDepth_exact _ _).mp (Nat.le_refl _) child
        (List.mem_flatMap.mpr ⟨row, member, selected⟩)

/-- Every actual original union member has depth at most the raw normalized union result's depth. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (context : Context before environment) (raw : Value Symbol Guard)
    (actual : build (.union expressions) environment before = .done raw after) :
    ∃ members middle,
      buildMany expressions environment before = .done members middle ∧
      run (makeUnion members) middle = (raw, after) ∧ Context middle environment ∧
      ∀ member ∈ members, member.depth ≤ raw.depth := by
  cases built : buildMany expressions environment before with
  | pending key state => simp only [build, built, Outcome.bind] at actual; cases actual
  | done members middle =>
      simp only [build, built, Outcome.bind, work, Outcome.done.injEq] at actual
      have made : run (makeUnion members) middle = (raw, after) := Prod.ext actual.1 actual.2
      have middleContext : Context middle environment := by
        simpa only [built, Outcome.state] using context.many expressions
      have available := (buildMany_verified expressions environment before context.base.normal.facts
        context.base.inputs).result members middle built
      have depth := InternedNormalizationDepthExact.makeUnion_depth members middle
        middleContext.base.normal.facts.coherent middleContext.base.normal.facts.cached
        middleContext.base.normal.facts.linked middleContext.base.normal.live available
      rw [made] at depth
      refine ⟨members, middle, rfl, made, middleContext, ?_⟩
      intro member selected
      rw [depth]
      exact (maximumDepth_exact _ _).mp (Nat.le_refl _) member selected

end MicroCFTA.SourceCurrentSourceChildDepth
