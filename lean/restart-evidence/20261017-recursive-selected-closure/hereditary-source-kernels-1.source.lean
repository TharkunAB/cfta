import MicroCFTA.SourceCurrentHereditaryUnconstrained

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.HereditaryUnconstrainedIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (NodeKey Reference)
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryUnconstrained
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Top" => (SourceEqualityConstraintConstructors.top : Guard)

private theorem top_plain : SourceMemoGate.plain Top = true := by
  simp [SourceMemoGate.plain, SourceEqualityConstraintConstructors.top,
    SourceCompactGuards.sourceEqualities, SourceCompactGuards.positiveNormalized]

/-- A recursive stored body is sufficient even when both probes are arbitrary. -/
theorem mu_union_ignores_probes (muEntry unionEntry nodeEntry : Interned NodeKey)
    (symbol : Symbol) (edgeIdentity : Nat) (depthProbe ordinaryProbe : Value Symbol Guard) (seen : List Nat) :
    let child : Value Symbol Guard := .reference (.interned muEntry.identity)
    let edge : EdgeValue Symbol Guard := .mk ⟨edgeIdentity, ⟨symbol, [child.referenceOf], Top⟩⟩ [child]
    let body : Value Symbol Guard := .union unionEntry [.node nodeEntry [edge] 0 [(.interned muEntry.identity)]]
      0 [(.interned muEntry.identity)]
    let value : Value Symbol Guard := .mu muEntry body depthProbe ordinaryProbe
    Annotated Plain body ∧
      SourceMemoGate.unconstrained value = true ∧
      (InternedSourceCrush.visit SourceMemoGate.plain value seen).1 = true := by
  dsimp only
  let child : Value Symbol Guard := .reference (.interned muEntry.identity)
  let edge : EdgeValue Symbol Guard := .mk ⟨edgeIdentity, ⟨symbol, [child.referenceOf], Top⟩⟩ [child]
  have node : Annotated Plain (.node nodeEntry [edge] 0 [(.interned muEntry.identity)] : Value Symbol Guard) := by
    apply Annotated.node
    · intro candidate member
      obtain rfl := List.mem_singleton.mp member
      exact top_plain
    · intro value member
      have same : value = child := by simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        EdgeValue.children, List.mem_singleton] using member
      subst value
      exact .reference _
  have body : Annotated Plain (.union unionEntry [.node nodeEntry [edge] 0 [(.interned muEntry.identity)]]
      0 [(.interned muEntry.identity)] : Value Symbol Guard) :=
    .union _ _ _ _ (fun value member => (List.mem_singleton.mp member) ▸ node)
  have annotated := Annotated.mu muEntry _ depthProbe ordinaryProbe body
  exact ⟨mu_body annotated, unconstrained _ annotated, annotated_visit SourceMemoGate.plain _ annotated seen⟩

/-- Original binder syntax constructs its own annotation, source gate, and physical Region. -/
theorem constructed_recursive_gate [DecidableEq (EdgeKey Symbol Guard)] (symbol base : Symbol) (smart : Bool) :
    let expression : InternedNestedConstruction.Syntax Symbol Guard := .binder smart (.union
      [.node [.mk symbol Top [.var 0]], .node [.mk base Top []]])
    ∃ value state, InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      Annotated Plain value ∧ SourceMemoGate.unconstrained value = true ∧
      SourceEqualityPartialPlainRegion.Region value := by
  dsimp only
  let expression : InternedNestedConstruction.Syntax Symbol Guard := .binder smart (.union
      [.node [.mk symbol Top [.var 0]], .node [.mk base Top []]])
  have allowed : SourceEqualityAnnotationConstruction.Allowed Plain expression := by
    simp [expression, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.ManyAllowed, SourceEqualityAnnotationConstruction.EdgesAllowed, top_plain]
  obtain ⟨value, state, built, _, annotated⟩ := SourceEqualityAnnotationConstruction.closed Plain expression allowed
  have ready := SourceEqualityRequiredCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  exact ⟨value, state, built, annotated, unconstrained _ annotated,
    to_plain_region state ready.semantic.1.normal.facts value annotated available closed⟩

/-- Empty effective equalities alone do not remove the source residual test. -/
theorem reflexive_same_is_residual :
    let guard : Guard := ⟨some [], .same [0] [0]⟩
    SourceCompactGuards.sourceEqualities guard = some [] ∧
      SourceEqualityPhysicalPayload.own guard = .ok (some []) ∧ SourceMemoGate.plain guard = false := by
  simp [SourceCompactGuards.sourceEqualities, SourceCompactGuards.positiveNormalized,
    SourceEqualityPhysicalPayload.own, SourceEqualityPhysicalPayload.read,
    SourceEqualityClassOrder.recordsOf, SourceMemoGate.plain]

#print axioms mu_union_ignores_probes
#check @mu_union_ignores_probes
#print axioms constructed_recursive_gate
#check @constructed_recursive_gate
#print axioms reflexive_same_is_residual
#check @reflexive_same_is_residual
end MicroCFTA.HereditaryUnconstrainedIndependentChecks
