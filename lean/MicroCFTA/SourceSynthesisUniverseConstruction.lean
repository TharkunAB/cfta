import MicroCFTA.SourceSynthesisUniverseOrigins
import MicroCFTA.SourceSynthesisUniverseNativeInput
import MicroCFTA.InternedFreshOrdinaryCoverage

/-!
# Complete constructor execution for original FirstOrder instructions

The source instruction contains finite node and union prefixes over one
computed type universe. Its repaired constructor schedule completes from
empty caches. The result derives its actual records and cache histories.
This is a source constructor model. Native Haskell demand, generated
intersection closure, and a total-work bound remain separate obligations.
-/
namespace MicroCFTA.SourceSynthesisUniverseConstruction
open SourceSynthesisTypeSyntax SourceSynthesisFirstOrderConstruction
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniverseOrigins
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome work)

variable [DecidableEq (EdgeKey String Guard)]

/-- A complete incoming cache suffices for the literal repaired schedule. -/
private def Completes (expression : Expression) : Prop :=
  ∀ state : State String Guard, Valid state → InternedRecordCoherence.Covered [] state →
    ∃ value final, InternedFreshOrdinaryConstruction.build expression [] state = .done value final

private theorem many_complete (expressions : List Expression) :
    (∀ expression ∈ expressions, Completes expression) →
    ∀ state : State String Guard, Valid state → InternedRecordCoherence.Covered [] state →
      ∃ values final, InternedFreshOrdinaryConstruction.buildMany expressions [] state = .done values final := by
  induction expressions with
  | nil => intro _ state _ _; exact ⟨[], state, by simp only [InternedFreshOrdinaryConstruction.buildMany]⟩
  | cons first rest ih =>
      intro checked state valid covered
      obtain ⟨value, after, head⟩ := checked first List.mem_cons_self state valid covered
      have afterValid : Valid after := by
        simpa only [head, Outcome.state] using
          (InternedFreshOrdinaryGrowth.build_correct first [] state valid).1
      have afterCovered := InternedFreshOrdinaryCoverage.build_covered first [] state valid covered
        value after head
      obtain ⟨values, final, tail⟩ := ih
        (fun expression member => checked expression (List.mem_cons_of_mem _ member))
        after afterValid afterCovered
      exact ⟨value :: values, final, by
        simp only [InternedFreshOrdinaryConstruction.buildMany, head, Outcome.bind, tail]⟩

private theorem edges_complete (rows : List Row) :
    (∀ row ∈ rows, Children Completes row) →
    ∀ state : State String Guard, Valid state → InternedRecordCoherence.Covered [] state →
      ∃ values final, InternedFreshOrdinaryConstruction.buildEdges rows [] state = .done values final := by
  induction rows with
  | nil => intro _ state _ _; exact ⟨[], state, by simp only [InternedFreshOrdinaryConstruction.buildEdges]⟩
  | cons first rest ih =>
      cases first with
      | mk symbol guard children =>
          intro checked state valid covered
          obtain ⟨values, afterChildren, childrenDone⟩ := many_complete children
            (checked _ List.mem_cons_self) state valid covered
          have childrenValid : Valid afterChildren := by
            simpa only [childrenDone, Outcome.state] using
              (InternedFreshOrdinaryGrowth.buildMany_correct children [] state valid).1
          have childrenCovered := InternedFreshOrdinaryCoverage.buildMany_covered children [] state
            valid covered values afterChildren childrenDone
          let allocated := run (makeEdge symbol guard values) afterChildren
          have edgeValid : Valid allocated.2 := (run_correct _ afterChildren childrenValid).1
          have edgeCovered : InternedRecordCoherence.Covered [] allocated.2 :=
            InternedNestedCoverage.run_covered _ afterChildren childrenValid childrenCovered
          obtain ⟨edges, final, tail⟩ := ih
            (fun row member => checked row (List.mem_cons_of_mem _ member))
            allocated.2 edgeValid edgeCovered
          dsimp only [allocated] at tail
          exact ⟨allocated.1 :: edges, final, by
            simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind,
              work, tail]
            rfl⟩

private theorem node_complete (rows : List Row)
    (checked : ∀ row ∈ rows, Children Completes row) : Completes (.node rows) := by
  intro state valid covered
  obtain ⟨values, after, done⟩ := edges_complete rows checked state valid covered
  exact ⟨(run (makeNode values) after).1, (run (makeNode values) after).2, by
    simp only [InternedFreshOrdinaryConstruction.build, done, Outcome.bind, work]⟩

private theorem union_complete (members : List Expression)
    (checked : ∀ member ∈ members, Completes member) : Completes (.union members) := by
  intro state valid covered
  obtain ⟨values, after, done⟩ := many_complete members checked state valid covered
  exact ⟨(run (makeUnion values) after).1, (run (makeUnion values) after).2, by
    simp only [InternedFreshOrdinaryConstruction.build, done, Outcome.bind, work]⟩

/-- Every finite prefix over the actual universe completes in a covered cache. -/
theorem overUniverse_complete (catalog : List (String × Nat)) (expression : Expression)
    (origin : OverUniverse (allTypes top catalog) expression)
    (state : State String Guard) (valid : Valid state)
    (covered : InternedRecordCoherence.Covered [] state) :
    ∃ value final, InternedFreshOrdinaryConstruction.build expression [] state = .done value final := by
  have complete : Completes expression := by
    induction origin with
    | atom =>
        intro state valid covered
        exact SourceSynthesisUniverseNativeInput.allTypes_complete top catalog [] state valid covered
    | node rows _ ih => exact node_complete rows ih
    | union members _ ih => exact union_complete members ih
  exact complete state valid covered

/-- The empty-cache prefix run derives its coherent records and both histories. -/
theorem overUniverse_closed_verified_complete (catalog : List (String × Nat))
    (expression : Expression) (origin : OverUniverse (allTypes top catalog) expression) :
    ∃ value final, InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ Grows empty final ∧
      Cache.Extends (empty (Symbol := String) (Guard := Guard)).nodes.issued final.nodes.issued := by
  obtain ⟨value, final, done⟩ := overUniverse_complete catalog expression origin empty empty_valid
    InternedRecordCoherence.empty_correct.2
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  exact ⟨value, final, done,
    by simpa only [done, Outcome.state] using checked.facts,
    checked.result value final done,
    by simpa only [done, Outcome.state] using checked.growth,
    by simpa only [done, Outcome.state] using checked.history⟩

/-- Actual original FirstOrder instructions complete the repaired constructor model. -/
theorem firstOrderRaw_constructor_complete (lib : Library) (query : Query) (size : Int)
    (expression : Expression) (returned : firstOrderRaw lib query size = .ok expression) :
    ∃ value final, InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ Grows empty final ∧
      Cache.Extends (empty (Symbol := String) (Guard := Guard)).nodes.issued final.nodes.issued := by
  exact overUniverse_closed_verified_complete (constructorCatalog lib query) expression
    (firstOrderRaw_overUniverse lib query size expression returned)

/-- The original constructor keeps its errors and supplies complete records on success. -/
theorem firstOrderRaw_constructor_result (lib : Library) (query : Query) (size : Int) :
    match firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ value final, InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
          Facts final ∧ Available final value ∧ Grows empty final ∧
          Cache.Extends (empty (Symbol := String) (Guard := Guard)).nodes.issued final.nodes.issued := by
  cases returned : firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact firstOrderRaw_constructor_complete lib query size expression returned

end MicroCFTA.SourceSynthesisUniverseConstruction
