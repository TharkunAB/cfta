import MicroCFTA.SourceMergedComparisonNumeric
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceEqualityProjectionPathDomain

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace MicroCFTA.ComparisonNumericIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceMergedComparisonNumeric (comparisonFuel)
open SourceCurrentAllocatedUnfoldHistory (heapBound Fits)
open MergedFreshOrdinaryComparison (check)
open MergedSourceComparison (Result)
local notation "initialMass" => InternedValueMassHeap.initialBound

private def recursive : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [], .mk 1 false [.var 0]])

private def expression : Syntax Nat Bool :=
  .node [.mk 9 true [recursive, .union [recursive, .node [.mk 3 false []]]]]

private def operands : Value Nat Bool → Value Nat Bool × Value Nat Bool
  | .node _ [.mk _ [wide, narrow]] _ _ => (wide, narrow)
  | _ => (.empty, .empty)

private def observed (input : Value Nat Bool) (source : State Nat Bool) : Prop :=
  let wide := (operands input).1
  let narrow := (operands input).2
  wide ∈ InternedProbeProvenance.children input ∧ narrow ∈ InternedProbeProvenance.children input ∧ wide.free = [] ∧ narrow.free = [] ∧
    (match wide with | .mu .. => True | _ => False) ∧
    (match narrow with | .union .. => True | _ => False) ∧
    match check id 16 [] wide narrow source with
    | .failed .. => False
    | .done answer after => answer = false ∧ source.nodes.next < after.nodes.next ∧
        check id 16 [] wide narrow after = .done answer after

private theorem literal : match InternedFreshOrdinaryConstruction.build expression [] empty with
    | .pending .. => False
    | .done input source => observed input source := by
  set_option cbv.maxSteps 200000000 in cbv
  simp

/-- Initial source facts construct an allocating Mu/union comparison and exact warm replay. -/
theorem constructed_mixed :
    ∃ input source wide narrow after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      wide = (operands input).1 ∧ narrow = (operands input).2 ∧
      (match wide with | .mu .. => True | _ => False) ∧
      (match narrow with | .union .. => True | _ => False) ∧
      check id (comparisonFuel source.nodes.next source.edges.next (initialMass source)) [] wide narrow source = .done false after ∧
      SourceMergedComparisonEffects.Effect source after ∧
      Fits (heapBound source.nodes.next source.edges.next (initialMass source)) after ∧
      SourceMergedComparisonMass.Resources
        (SourceMergedComparisonMass.comparisonBound
          (comparisonFuel source.nodes.next source.edges.next (initialMass source)) (initialMass source)) source after ∧
      source.nodes.next < after.nodes.next ∧
      (∀ extra, check id (comparisonFuel source.nodes.next source.edges.next (initialMass source) + extra)
        [] wide narrow source = .done false after) ∧
      check id (comparisonFuel source.nodes.next source.edges.next (initialMass source) + 16)
        [] wide narrow after = .done false after ∧
      ¬ MergedColdReaderClosedInputs.ClosedValues [wide, narrow, .reference .depth] ∧
      SourceEqualityProjectionPathDomain.ForestClosed [0] [wide, narrow, .reference .depth] ∧
      SourceEqualityProjectionPathDomain.ForestClosed [1] [wide, narrow, .reference .depth] := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input source built
  have stored := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  have shape := literal
  rw [built] at shape
  change observed input source at shape
  rcases shape with ⟨wideMember, narrowMember, wideClosed, narrowClosed, wideMu, narrowUnion, computed⟩
  have wideInput := available.children _ wideMember
  have narrowInput := available.children _ narrowMember
  obtain ⟨answer, after, done, effects, fits, resources, stable⟩ := SourceMergedComparisonNumeric.check_complete
    id source (initialMass source) semantic stored [] (operands input).1 (operands input).2
    wideInput narrowInput wideClosed narrowClosed
  cases small : check id 16 [] (operands input).1 (operands input).2 source with
  | failed => simp only [small] at computed
  | done actual final =>
      simp only [small] at computed
      rcases computed with ⟨answerFalse, changes, warm⟩
      have same := (stable 16).symm.trans (by
        simpa only [Nat.add_comm] using
          (SourceMergedComparisonStability.check_stable id 16
            (comparisonFuel source.nodes.next source.edges.next (initialMass source)) []
            (operands input).1 (operands input).2 source actual final small).trans small)
      rcases Result.done.inj same with ⟨answerEq, heapEq⟩
      subst actual
      subst final
      subst answer
      have warmLarge := (SourceMergedComparisonStability.check_stable id 16
        (comparisonFuel source.nodes.next source.edges.next (initialMass source)) []
        (operands input).1 (operands input).2 after false after warm).trans warm
      refine ⟨input, source, (operands input).1, (operands input).2, after, built, rfl, rfl,
        wideMu, narrowUnion, done, effects, fits, resources, changes, stable, ?_, ?_, ?_, ?_⟩
      · simpa only [Nat.add_comm] using warmLarge
      · intro allClosed
        have impossible := allClosed (.reference .depth) (by simp)
        cases impossible
      · simpa [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
          SourceEqualityProjectionGraph.select] using wideClosed
      · simpa [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
          SourceEqualityProjectionGraph.select] using narrowClosed

end MicroCFTA.ComparisonNumericIntegration

#print axioms MicroCFTA.ComparisonNumericIntegration.constructed_mixed
#check @MicroCFTA.ComparisonNumericIntegration.constructed_mixed
