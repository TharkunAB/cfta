import MicroCFTA.SourceMemoGate
import MicroCFTA.SourceEqualityPartialPlainAnnotations
import MicroCFTA.InternedSourceCrushSemantics

/-!
# Hereditary source guards and the actual unconstrained read

The existing annotation predicate visits every ordinary edge and the stored
Mu body. The source crush can skip a repeated identity. It reads neither Mu
probe. The source plain test retains both effective equalities and residual
syntax. A structural plain region also needs physical available closed input.
-/
namespace MicroCFTA.SourceCurrentHereditaryUnconstrained
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceEqualityAnnotationLanguage

/-- Pointwise annotation implication preserves the existing hereditary predicate. -/
theorem annotated_mono {first second : Guard → Prop} {value : Value Symbol Guard}
    (implies : ∀ guard, first guard → second guard) (annotated : Annotated first value) :
    Annotated second value := by
  induction annotated with
  | empty => exact .empty
  | reference name => exact .reference name
  | node entry edges depth free guards children ih =>
      exact .node entry edges depth free (fun edge member => implies _ (guards edge member)) ih
  | union entry members depth free children ih => exact .union entry members depth free ih
  | mu entry body depth ordinary annotated ih => exact .mu entry body depth ordinary ih

/-- Each actual ordinary row retains its guard and all child annotations. -/
theorem node_edge {valid : Guard → Prop} {value : Value Symbol Guard}
    (annotated : Annotated valid value) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ InternedEdgeResidency.nodeEdges value) :
    valid edge.entry.key.constraint ∧ ∀ child ∈ edge.children, Annotated valid child := by
  cases annotated with
  | node entry edges depth free guards children =>
      exact ⟨guards edge member, fun child present => children child (List.mem_flatMap.mpr ⟨edge, member, present⟩)⟩
  | empty | reference | union | mu => cases member

/-- Every source traversal child retains the same complete annotation predicate. -/
theorem source_child {valid : Guard → Prop} {value : Value Symbol Guard}
    (annotated : Annotated valid value) (child : Value Symbol Guard)
    (member : child ∈ InternedSourceCrush.sourceChildren value) : Annotated valid child := by
  cases annotated with
  | empty | reference => cases member
  | node entry edges depth free guards children => exact children child member
  | union entry members depth free children => exact children child member
  | mu entry body depth ordinary annotated => exact (List.mem_singleton.mp member) ▸ annotated

/-- A union member retains annotations without unfolding any reference. -/
theorem union_member {valid : Guard → Prop} {entry members depth free}
    (annotated : Annotated valid (.union entry members depth free : Value Symbol Guard))
    (child : Value Symbol Guard) (member : child ∈ members) : Annotated valid child :=
  source_child annotated child member

/-- A Mu projection reads only its stored body. Neither probe needs an annotation premise. -/
theorem mu_body {valid : Guard → Prop} {entry body depth ordinary}
    (annotated : Annotated valid (.mu entry body depth ordinary : Value Symbol Guard)) : Annotated valid body :=
  source_child annotated body List.mem_cons_self

private theorem visit_many_true (plain : Guard → Bool) (values : List (Value Symbol Guard))
    (all : ∀ value ∈ values, ∀ seen, (InternedSourceCrush.visit plain value seen).1 = true)
    (seen : List Nat) : (InternedSourceCrush.visitMany plain values seen).1 = true := by
  induction values generalizing seen with
  | nil => simp only [InternedSourceCrush.visitMany]
  | cons first rest ih =>
      simp only [InternedSourceCrush.visitMany, all first List.mem_cons_self,
        ih (fun value member => all value (List.mem_cons_of_mem _ member)), Bool.and_self]

private theorem visit_edges_true (plain : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (all : ∀ value ∈ edges.flatMap EdgeValue.children, ∀ seen, (InternedSourceCrush.visit plain value seen).1 = true)
    (seen : List Nat) : (InternedSourceCrush.visitEdges plain edges seen).1 = true := by
  induction edges generalizing seen with
  | nil => simp only [InternedSourceCrush.visitEdges]
  | cons edge rest ih =>
      cases edge with
      | mk entry children =>
          simp only [InternedSourceCrush.visitEdges]
          rw [visit_many_true plain children
            (fun value member => all value (List.mem_flatMap.mpr ⟨.mk entry children, List.mem_cons_self, member⟩)),
            ih (fun value member => all value (List.mem_flatMap.mpr (by
              obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
              exact ⟨edge, List.mem_cons_of_mem _ present, inside⟩)))]
          rfl

/-- Hereditary true guards make the literal visited fold true for every initial visited set. -/
theorem annotated_visit (plain : Guard → Bool) (value : Value Symbol Guard)
    (annotated : Annotated (fun guard => plain guard = true) value) (seen : List Nat) :
    (InternedSourceCrush.visit plain value seen).1 = true := by
  induction annotated generalizing seen with
  | empty | reference => simp only [InternedSourceCrush.visit]
  | node entry edges depth free guards children ih =>
      rw [InternedSourceCrush.visit]
      split
      · rfl
      · simp only [List.all_eq_true.mpr guards, visit_edges_true plain edges ih, Bool.and_self]
  | union entry members depth free children ih =>
      rw [InternedSourceCrush.visit]
      split
      · rfl
      · exact visit_many_true plain members ih _
  | mu entry body depth ordinary annotated ih =>
      rw [InternedSourceCrush.visit]
      split
      · rfl
      · exact ih _

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The actual edge test requires empty effective equalities, including positive extraction. -/
theorem plain_equalities (guard : Guard) (plain : SourceMemoGate.plain guard = true) :
    SourceCompactGuards.sourceEqualities guard = some [] :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp plain).1

/-- The actual residual test accepts exactly the supported positive syntax. -/
theorem plain_positive (guard : Guard) (plain : SourceMemoGate.plain guard = true) :
    (SourceCompactGuards.positiveNormalized guard.guard).isSome = true :=
  (Bool.and_eq_true_iff.mp plain).2

/-- A true source edge test derives the literal empty physical own payload. -/
theorem plain_physical (guard : Guard) (plain : SourceMemoGate.plain guard = true) :
    SourceEqualityPhysicalPayload.own guard = .ok (some []) :=
  SourceEqualityPartialPlainAnnotations.physical (plain_equalities guard plain)

/-- The hereditary annotation condition implies the actual source memo-gate result. -/
theorem unconstrained (value : Value Symbol Guard)
    (annotated : Annotated (fun guard => SourceMemoGate.plain guard = true) value) :
    SourceMemoGate.unconstrained value = true :=
  annotated_visit SourceMemoGate.plain value annotated []

/-- Physical available closed annotations derive the existing plain caller Region. -/
theorem to_plain_region (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (annotated : Annotated (fun guard => SourceMemoGate.plain guard = true) value)
    (available : Available state value) (closed : value.free = []) :
    SourceEqualityPartialPlainRegion.Region value :=
  SourceEqualityPartialPlainAnnotations.annotated state facts value
    (annotated_mono plain_equalities annotated) available closed

end MicroCFTA.SourceCurrentHereditaryUnconstrained


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
        edge, EdgeValue.children, List.mem_singleton] using member
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
