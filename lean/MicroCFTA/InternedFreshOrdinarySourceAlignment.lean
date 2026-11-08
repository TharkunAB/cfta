import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Ordered source calls of the fresh constructor

Completed list construction retains one actual call for each source position.
Each call starts with source facts and available environment values. Edge
alignment also retains the child call, allocation, and complete row fields.
-/
namespace MicroCFTA.InternedFreshOrdinarySourceAlignment
open Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)

/-- Each completed child value has its ordered source call at its actual entry heap. -/
theorem buildMany_calls [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (facts : Facts before) (inputs : Values before environment)
    (done : buildMany expressions environment before = .done values after) :
    All₂ (fun expression value => ∃ start finish,
      Facts start ∧ Values start environment ∧ build expression environment start = .done value finish)
      expressions values := by
  induction expressions generalizing before values after with
  | nil =>
      have same : [] = values ∧ before = after := by
        simpa only [buildMany, Outcome.done.injEq] using done
      rcases same with ⟨rfl, rfl⟩
      exact .nil
  | cons first rest ih =>
      cases head : build first environment before with
      | pending key current =>
          simp only [buildMany, head, Outcome.bind] at done
          cases done
      | done value middle =>
          have checked := InternedFreshOrdinaryFacts.build_verified first environment before facts inputs
          have middleFacts : Facts middle := by
            simpa only [head, Outcome.state] using checked.facts
          have middleInputs : Values middle environment := by
            intro item member
            simpa only [head, Outcome.state] using checked.available item (inputs item member)
          cases tail : buildMany rest environment middle with
          | pending key current =>
              simp only [buildMany, head, Outcome.bind, tail] at done
              cases done
          | done remaining final =>
              have same : value :: remaining = values ∧ final = after := by
                simpa only [buildMany, head, Outcome.bind, tail, Outcome.done.injEq] using done
              rcases same with ⟨rfl, rfl⟩
              exact .cons ⟨before, middle, facts, inputs, head⟩
                (ih middle remaining final middleFacts middleInputs tail)

/-- One source edge retains its actual child call, constructor call, and literal fields. -/
def EdgeCall [DecidableEq (EdgeKey Symbol Guard)] (environment : List (Value Symbol Guard)) :
    EdgeSyntax Symbol Guard → EdgeValue Symbol Guard → Prop
  | .mk symbol guard children, edge =>
      ∃ start middle next values, Facts start ∧ Values start environment ∧
        buildMany children environment start = .done values middle ∧
        run (makeEdge symbol guard values) middle = (edge, next) ∧
        edge.entry.key.symbol = symbol ∧ edge.entry.key.constraint = guard ∧ edge.children = values

/-- Every completed source row list retains the same ordered edge-call alignment. -/
theorem buildEdges_calls [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (outputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (facts : Facts before) (inputs : Values before environment)
    (done : buildEdges expressions environment before = .done outputs after) :
    All₂ (EdgeCall environment) expressions outputs := by
  induction expressions generalizing before outputs after with
  | nil =>
      have same : [] = outputs ∧ before = after := by
        simpa only [buildEdges, Outcome.done.injEq] using done
      rcases same with ⟨rfl, rfl⟩
      exact .nil
  | cons expression rest ih =>
      cases expression with
      | mk symbol guard children =>
          cases childDone : buildMany children environment before with
          | pending key current =>
              simp only [buildEdges, childDone, Outcome.bind] at done
              cases done
          | done values middle =>
              have childChecked := InternedFreshOrdinaryFacts.buildMany_verified children environment before facts inputs
              have middleFacts : Facts middle := by
                simpa only [childDone, Outcome.state] using childChecked.facts
              have available := childChecked.result values middle childDone
              have edgeChecked := edge_verified symbol guard values middle middleFacts available
              let made := run (makeEdge symbol guard values) middle
              have nextFacts : Facts made.2 := edgeChecked.facts
              have nextInputs : Values made.2 environment := by
                intro item member
                have current : Available middle item := by
                  simpa only [childDone, Outcome.state] using childChecked.available item (inputs item member)
                exact edgeChecked.available item current
              cases tail : buildEdges rest environment made.2 with
              | pending key current =>
                  simp only [buildEdges, childDone, Outcome.bind, work] at done
                  change (buildEdges rest environment made.2).bind
                    (fun remaining final => .done (made.1 :: remaining) final) = .done outputs after at done
                  simp only [tail, Outcome.bind] at done
                  cases done
              | done remaining final =>
                  simp only [buildEdges, childDone, Outcome.bind, work] at done
                  change (buildEdges rest environment made.2).bind
                    (fun remaining final => .done (made.1 :: remaining) final) = .done outputs after at done
                  simp only [tail, Outcome.bind, Outcome.done.injEq] at done
                  obtain ⟨rfl, rfl⟩ := done
                  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleFacts symbol guard values available
                  exact .cons ⟨before, middle, made.2, values, facts, inputs, childDone, rfl,
                    fields.1, fields.2.1, fields.2.2⟩
                    (ih made.2 remaining final nextFacts nextInputs tail)

end MicroCFTA.InternedFreshOrdinarySourceAlignment
