import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
import MicroCFTA.SourceSynthesisUniverseCurrentCallerBoundary

/-!
# Program roles for the actual ordinary-symbol caller input

The literal name map is the source name paired with refinement Top.
Its syntax map equals the existing caller adapter. Actual caller receipts
supply the fresh Label build; no String heap or identity is transported.
General signed Library and Query requests also derive their fresh results.
The concrete caller existence result retains its checked source receipt.
These results do not establish roles after the caller starts narrowing.
-/
namespace MicroCFTA.SourceSynthesisLabelProgramBuildRoles
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression Row)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

/-- Source ordinary symbols retain their name and use refinement Top. -/
def literal (name : String) : Symbol := (name, .top)

mutual
/-- The generic name map equals the literal existing caller syntax adapter. -/
theorem mapSyntax_ordinarySymbols (expression : Expression) :
    SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression =
      SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression := by
  cases expression with
  | empty | var => rfl
  | node rows =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax,
        SourceSynthesisUniverseCallerBoundary.ordinarySymbols, mapEdges_ordinaryEdges rows]
  | union members =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax,
        SourceSynthesisUniverseCallerBoundary.ordinarySymbols, mapChildren_ordinaryChildren members]
  | binder smart body =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax,
        SourceSynthesisUniverseCallerBoundary.ordinarySymbols, mapSyntax_ordinarySymbols body]
termination_by sizeOf expression

/-- The name adapter retains every original child position. -/
theorem mapChildren_ordinaryChildren (expressions : List Expression) :
    SourceSynthesisProgramBuildRolesGeneric.mapChildren literal expressions =
      SourceSynthesisUniverseCallerBoundary.ordinaryChildren expressions := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapChildren,
        SourceSynthesisUniverseCallerBoundary.ordinaryChildren,
        mapSyntax_ordinarySymbols first, mapChildren_ordinaryChildren rest]
termination_by sizeOf expressions

/-- The name adapter retains each complete guard and ordered row. -/
theorem mapEdges_ordinaryEdges (rows : List Row) :
    SourceSynthesisProgramBuildRolesGeneric.mapEdges literal rows =
      SourceSynthesisUniverseCallerBoundary.ordinaryEdges rows := by
  cases rows with
  | nil => rfl
  | cons row rest =>
      cases row with
      | mk name guard children =>
          simp only [SourceSynthesisProgramBuildRolesGeneric.mapEdges,
            SourceSynthesisUniverseCallerBoundary.ordinaryEdges, literal,
            mapChildren_ordinaryChildren children, mapEdges_ordinaryEdges rest]
termination_by sizeOf rows
end

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private theorem built_roles (value : Value Symbol Guard) (heap : State Symbol Guard)
    (done : InternedFreshOrdinaryConstruction.build SourceSynthesisUniverseCallerBoundary.expression [] empty =
      .done value heap) :
    Facts heap ∧ Available heap value ∧ SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued := by
  have sourceRole := SourceSynthesisProgramRoles.firstOrderRaw_roles
    SourceSynthesisUniverseRequiredBoundary.library SourceSynthesisUniverseRequiredBoundary.query 2
    SourceSynthesisUniverseRequiredBoundary.expression SourceSynthesisUniverseRequiredBoundary.source_accepts
  have roles := SourceSynthesisProgramBuildRolesGeneric.build_mapped_program literal
    SourceSynthesisUniverseRequiredBoundary.expression sourceRole [] empty value heap empty_facts
    (by intro child member; cases member)
    (by simpa only [mapSyntax_ordinarySymbols, SourceSynthesisUniverseCallerBoundary.expression] using done)
  have verified := InternedFreshOrdinaryFacts.closed_verified SourceSynthesisUniverseCallerBoundary.expression
  exact ⟨by simpa only [done, Outcome.state] using verified.facts,
    verified.result value heap done, roles,
    by simpa only [done, Outcome.state] using verified.growth,
    by simpa only [done, Outcome.state] using verified.history⟩

/-- The earlier literal caller receipt derives roles from its own actual fresh heap. -/
theorem caller_receipt_roles (observed : SourceSynthesisUniverseCallerBoundary.Receipt)
    (found : SourceSynthesisUniverseCallerBoundary.observation = some observed) :
    Facts observed.heap ∧ Available observed.heap observed.root ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal observed.root ∧
      Grows empty observed.heap ∧
      Cache.Extends (empty : State Symbol Guard).nodes.issued observed.heap.nodes.issued :=
  built_roles observed.root observed.heap (SourceSynthesisUniverseCallerBoundary.observation_receipts observed found).1

/-- The current allocated caller receipt derives the same roles on its actual initial root. -/
theorem current_receipt_roles (observed : SourceSynthesisUniverseCurrentCallerBoundary.Receipt)
    (found : SourceSynthesisUniverseCurrentCallerBoundary.observation = some observed) :
    Facts observed.heap ∧ Available observed.heap observed.root ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal observed.root ∧
      Grows empty observed.heap ∧
      Cache.Extends (empty : State Symbol Guard).nodes.issued observed.heap.nodes.issued :=
  built_roles observed.root observed.heap (SourceSynthesisUniverseCurrentCallerBoundary.observation_receipts observed found).2.1

/-- The checked concrete original request supplies its receipt and initial physical roles. -/
theorem actual_current_roles :
    ∃ observed : SourceSynthesisUniverseCurrentCallerBoundary.Receipt,
      SourceSynthesisUniverseCurrentCallerBoundary.observation = some observed ∧
      Facts observed.heap ∧ Available observed.heap observed.root ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal observed.root ∧
      Grows empty observed.heap ∧
      Cache.Extends (empty : State Symbol Guard).nodes.issued observed.heap.nodes.issued := by
  obtain ⟨observed, _owner, _application, _function, found, _rest⟩ :=
    SourceSynthesisUniverseCurrentCallerBoundary.actual_requests
  exact ⟨observed, found, current_receipt_roles observed found⟩

/-- Every accepted original request derives roles on its actual ordinary-symbol build. -/
theorem firstOrderRaw_build_roles (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (size : Int) (expression : Expression)
    (returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size = .ok expression) :
    ∃ value final,
      InternedFreshOrdinaryConstruction.build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression)
        [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty final ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued final.nodes.issued := by
  simpa only [mapSyntax_ordinarySymbols] using
    SourceSynthesisProgramBuildRolesGeneric.firstOrderRaw_build_roles literal lib query size expression returned

/-- Signed source errors remain explicit before ordinary-symbol construction. -/
theorem firstOrderRaw_build_result (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ value final,
          InternedFreshOrdinaryConstruction.build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression)
            [] empty = .done value final ∧
          Facts final ∧ Available final value ∧ SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
          Grows empty final ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued final.nodes.issued := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact firstOrderRaw_build_roles lib query size expression returned

end MicroCFTA.SourceSynthesisLabelProgramBuildRoles
