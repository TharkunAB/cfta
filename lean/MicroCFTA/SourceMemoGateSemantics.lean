import MicroCFTA.InternedSourceCrushCorrect
import MicroCFTA.SourceUnconstrainedMemo
import MicroCFTA.InternedFreshOrdinaryConstraintHeap

/-!
# Exact physical constraint meaning of the source gate predicate

The concrete source read checks exactly the ordinary edges reached through
stored bodies, ordinary children, and union members. Normalized source
annotations give the corresponding always-accepting guard meaning.
-/
namespace MicroCFTA.SourceMemoGate
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency
open SourceObservations SourceSymbolicIndex SourceGuards

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- The actual source node predicate checks exactly every physical ordinary descendant edge. -/
theorem unconstrained_exact (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    unconstrained value = true ↔ ∀ record, InternedSourceCrush.Reaches [value] record →
      ∀ edge ∈ nodeEdges record, plain edge.entry.key.constraint = true :=
  InternedSourceCrush.unconstrained_exact plain value state coherent available

/-- A false concrete source predicate supplies an actual reached nonplain edge. -/
theorem unconstrained_false (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    unconstrained value = false ↔ ∃ record, InternedSourceCrush.Reaches [value] record ∧
      ∃ edge ∈ nodeEdges record, plain edge.entry.key.constraint = false :=
  InternedSourceCrush.unconstrained_false plain value state coherent available

/-- The local source edge test gives an always-accepting constraint for normalized equality annotations. -/
theorem plain_accepts (edge : EdgeValue Symbol Guard)
    (active : SourceCompactGuards.ActiveOption edge.entry.key.constraint.equalities)
    (checked : plain edge.entry.key.constraint = true)
    (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula)
    (term : Language.Term Symbol) : acceptsConstraint formulas solver edge.entry.key.constraint term = true :=
  SourceCyclicAutomaton.unconstrained_plain formulas solver
    (⟨edge.entry.key.symbol, ([] : List Unit), edge.entry.key.constraint⟩ : SourceCyclicAutomaton.Row Unit FullSyntax.Formula)
    active checked term

/-- A concrete true source predicate gives always-accepting guards at every actual reached ordinary edge. -/
theorem reached_accepts (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state)
    (heap : InternedFreshOrdinaryConstraintHeap.Heap
      (fun constraint : Guard => SourceCompactGuards.ActiveOption constraint.equalities) state)
    (available : Available state value) (checked : unconstrained value = true)
    (record : Value Symbol Guard) (reached : InternedSourceCrush.Reaches [value] record)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ nodeEdges record)
    (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula) (term : Language.Term Symbol) :
    acceptsConstraint formulas solver edge.entry.key.constraint term = true := by
  have inputs : ∀ other ∈ [value], Available state other := by
    intro other selected
    exact (List.mem_singleton.mp selected) ▸ available
  have recordAvailable := reached.available state inputs
  have resident := resident_edges state facts.linked record recordAvailable.resident edge member
  exact plain_accepts edge (heap edge.entry.key edge resident)
    ((unconstrained_exact value state facts.coherent available).mp checked record reached edge member) formulas solver term

end MicroCFTA.SourceMemoGate
