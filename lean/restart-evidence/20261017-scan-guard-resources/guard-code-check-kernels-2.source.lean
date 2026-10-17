import MicroCFTA.SourceCurrentNativeGuardCode
import MicroCFTA.SourceEqualityNativeDemandControl
import MicroCFTA.SourceCurrentConjunctionGuard
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceEqualityPCSNativeEdge
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.GuardCodeCheck
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConjunctionRowsAllocation (Ready Tuple)
open SourceCurrentConjunctionWorklist (Run)
open SourceCurrentConjunctionGuardUniverse
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def raw : Guard := ⟨some [[[0],[1]]], .top⟩
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("step", .top) top [.var 0], .mk ("base", .top) top []])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("root", .top) raw [recursive, .union [recursive, .node [.mk ("leaf", .top) top []]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def seedBuild := SourceEqualityConstraintAllocation.construct raw.equalities Cache.emptyState
private def seedValue : SourceEqualityConstraintAllocation.Value := match seedBuild.1 with
  | .ok result => result | .error _ => .contradiction
private def seedState := SourceEqualityConstraintMemoAllocation.initial seedBuild.2
private def operations := SourceEqualityMkEdgeAllocation.emptyField seedState
private def before : Physical := ⟨heap, operations⟩
private def edge : EdgeValue Symbol Guard := (nodeEdges value).headD ⟨⟨0, ⟨("default", .top), [], top⟩⟩, []⟩

private theorem constructed : built = .done value heap := by cbv
private theorem semantic : SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression value heap constructed
private theorem available : Available heap value :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result value heap constructed
private theorem closed : value.free = [] := by cbv
private theorem cached : SourceEqualityGuardReadback.Cached raw.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem seed_constructed : seedBuild.1 = .ok seedValue := by cbv
private theorem seed_ready : SourceEqualityConstraintMemoAllocation.Valid seedState ∧
    SourceCurrentConjunctionEquality.FieldAvailable seedState raw := by
  obtain ⟨result, cache, done, valid, ready, _steps, read, _classes⟩ :=
    SourceEqualityConstraintAllocation.construct_complete raw.equalities cached Cache.emptyState Cache.empty_valid
  have same : result = seedValue := Except.ok.inj ((congrArg Prod.fst done).symm.trans seed_constructed)
  subst result
  have sameCache : cache = seedBuild.2 := (congrArg Prod.snd done).symm
  subst cache
  exact ⟨SourceEqualityConstraintMemoAllocation.initial_valid _ valid,
    SourceCurrentConjunctionFieldAllocation.of_receipt seedState raw cached seedValue ready read⟩
private theorem initial_ready : Ready before := by
  have fields := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) seedState seed_ready.1
  have rawAvailable := seed_ready.2.grows fields.2.1
  have annotation : SourceEqualityAnnotationHeap.Heap (SourceCurrentConjunctionEquality.FieldAvailable operations) heap := by
    have permitted : SourceEqualityAnnotationConstruction.Allowed
        (SourceCurrentConjunctionEquality.FieldAvailable operations) expression := by
      simp only [expression, recursive, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]
      repeat' first | exact rawAvailable | exact fields.2.2 | constructor
    simpa only [built, heap] using SourceEqualityAnnotationConstruction.build _ expression permitted [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
  exact ⟨semantic, InternedFreshOrdinaryCosts.closed_heap expression, fields.1, annotation⟩
private theorem initial_pending : SourceCurrentConjunctionWorklist.PendingReady before [[value],[.reference .depth]] := by
  intro nodes member child included
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have same := List.mem_singleton.mp included
    subst child
    exact available
  · have same := List.mem_singleton.mp included
    subst child
    exact reference_available heap .depth (by intro identity member; simp only [Value.free, List.mem_singleton] at member; cases member)
private theorem edge_member : edge ∈ nodeEdges value := by cbv; exact .head _
private theorem edge_resident : EdgeResident heap edge :=
  resident_edges heap semantic.ready.semantic.1.normal.facts.linked value available.resident edge edge_member
private theorem edge_closed : MergedColdReaderClosedInputs.ClosedEdges [edge] := by
  intro selected member
  have same := List.mem_singleton.mp member
  subst selected
  have allClosed : edge.children.all (fun child => child.free.isEmpty) = true := by cbv
  intro child included
  exact List.isEmpty_iff.mp (List.all_eq_true.mp allClosed child included)
private theorem source_inputs : InternedNestedProvenance.Values heap [value] := by
  intro selected member
  simpa only [List.mem_singleton.mp member] using available
private theorem positive_source : raw ∈ guards heap ∧ top ∈ guards heap := by
  constructor <;> (cbv; repeat' first | exact List.Mem.head _ | apply List.Mem.tail)
private theorem recursive_union :
    (match edge.children[0]? with | some (Value.mu _ _ _ _) => True | _ => False) ∧
    (match edge.children[1]? with | some (Value.union _ _ _ _) => True | _ => False) := by cbv


open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
private def request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, edge, edge⟩
private def current (width : Nat) : SourceEqualityNativeDemand.State width :=
  ⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩
private def emittedGuard (guard : Guard) : Prop := guard = top ∨
  guard = SourceEqualityPCSNativeEdge.conjoin edge.entry.key.constraint edge.entry.key.constraint

/-- Actual source construction and field loads produce the checked body and its local guard certificate. -/
theorem constructed_checked_body (width : Nat) :
    ((match edge.children[0]? with | some (Value.mu _ _ _ _) => True | _ => False) ∧
      (match edge.children[1]? with | some (Value.union _ _ _ _) => True | _ => False)) ∧
    ∃ (code : Code Symbol Guard (EdgeValue Symbol Guard)) (after : SourceEqualityNativeDemand.State width)
      (first : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula),
      EdgeResident (current width).native.machine.heap request.left ∧
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint (current width).operations.constraints =
        .ok (some first) ∧
      SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint (current width).operations.constraints =
        .ok (some first) ∧
      SourceEqualityConstraintAllocation.Ready (current width).operations.constraints first.stored ∧
      SourceEqualityConjoinAllocation.readback first = request.left.entry.key.constraint ∧
      body request Code.pure (current width) = .yielded (.code code) after ∧
      SourceCurrentNativeGuardCode.Fields emittedGuard code := by
  have fields := initial_ready.fields edge.entry.key edge edge_resident
  obtain ⟨first, loaded, fieldReady, readback, _built⟩ :=
    SourceCurrentConjunctionEquality.FieldAvailable.receipts fields initial_ready.valid
  obtain ⟨code, afterOperations, yielded⟩ := SourceEqualityNativeDemand.body_complete request Code.pure
    (current width) initial_ready.valid fields.1 fields.1 first first loaded loaded
  obtain ⟨emitted, same, certificate⟩ := SourceCurrentNativeGuardCode.body_fields emittedGuard request Code.pure
    (current width) {current width with operations := afterOperations} (.code code) initial_ready.valid
    ⟨fields.1, fields.1⟩ (Or.inl rfl) (Or.inr rfl) (fun _ => trivial) yielded
  rw [same] at yielded
  exact ⟨recursive_union, emitted, _, first, edge_resident, loaded, loaded, fieldReady, readback,
    yielded, certificate⟩

/-- A recursive source request emits no literal guard even when no guard satisfies the predicate. -/
theorem constructed_node_code :
    ((match edge.children[0]? with | some (Value.mu _ _ _ _) => True | _ => False) ∧
      (match edge.children[1]? with | some (Value.union _ _ _ _) => True | _ => False)) ∧
    SourceCurrentNativeGuardCode.Fields (fun _ => False)
      (compileNode (⟨IntersectionEmptyDomain.emptyDomain,
        edge.children[0]?.getD .empty, edge.children[1]?.getD .empty⟩ : NodeRequest Symbol Guard)) :=
  ⟨recursive_union, SourceCurrentNativeGuardCode.compileNode_fields (fun _ => False) _⟩

end MicroCFTA.GuardCodeCheck
#check @MicroCFTA.GuardCodeCheck.constructed_checked_body
#print axioms MicroCFTA.GuardCodeCheck.constructed_checked_body
#check @MicroCFTA.GuardCodeCheck.constructed_node_code
#print axioms MicroCFTA.GuardCodeCheck.constructed_node_code
