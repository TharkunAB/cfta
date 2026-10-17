import MicroCFTA.SourceCurrentConjunctionGuardUniverse
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

namespace MicroCFTA.GuardUniverseKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConjunctionRowsAllocation (Ready Tuple)
open SourceCurrentConjunctionWorklist (Run)
open SourceCurrentConjunctionGuardUniverse
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Nat FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def raw : Guard := ⟨some [[[0],[1]]], .top⟩
private def recursive : Syntax Nat Guard :=
  .binder false (.node [.mk 1 top [.var 0], .mk 2 top []])
private def expression : Syntax Nat Guard :=
  .node [.mk 0 raw [recursive, .union [recursive, .node [.mk 3 top []]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Nat Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def seedBuild := SourceEqualityConstraintAllocation.construct raw.equalities Cache.emptyState
private def seedValue : SourceEqualityConstraintAllocation.Value := match seedBuild.1 with
  | .ok result => result | .error _ => .contradiction
private def seedState := SourceEqualityConstraintMemoAllocation.initial seedBuild.2
private def operations := SourceEqualityMkEdgeAllocation.emptyField seedState
private def before : Physical := ⟨heap, operations⟩
private def edge : EdgeValue Nat Guard := (nodeEdges value).headD ⟨⟨0, ⟨0, [], top⟩⟩, []⟩

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
      exact ⟨rawAvailable, ⟨⟨fields.2.2, trivial, ⟨fields.2.2, trivial, trivial⟩⟩,
        ⟨⟨⟨fields.2.2, trivial, ⟨fields.2.2, trivial, trivial⟩⟩,
          ⟨⟨fields.2.2, trivial, trivial⟩, trivial⟩⟩, trivial⟩⟩, trivial⟩
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
    exact reference_available heap .depth (by intro identity member; cases member with | head impossible => cases impossible | tail _ impossible => cases impossible)
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
  constructor <;> (cbv; decide)
private theorem recursive_union :
    (match edge.children[0]? with | some (Value.mu _ _ _ _) => True | _ => False) ∧
    (match edge.children[1]? with | some (Value.union _ _ _ _) => True | _ => False) := by cbv

/-- Actual source construction retains its finite carrier through admission and an open skipped pending item. -/
theorem constructed_exploration :
    ∃ (query : Value Nat Guard) (initial : Physical)
      (final : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Nat Guard))) (after : Physical),
      query.free = [] ∧ raw.equalities = some [[[0],[1]]] ∧
      raw ∈ guards initial.heap ∧ top ∈ guards initial.heap ∧
      Run 3 [] [[query],[.reference .depth]] initial final after ∧ final ≠ [] ∧
      SourceCurrentConjunctionWorklist.TableReady after final ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ guards initial.heap) after.heap := by
  obtain ⟨final, after, actual, _effects, table, _bound, annotation⟩ :=
    entered 3 [[value],[.reference .depth]] before initial_ready initial_pending
  have nonempty : final ≠ [] := by
    have notEmpty : [value].any SourceCurrentConjunctionRequirements.isEmpty = false := by cbv
    have fresh : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
        SourceCurrentConjunctionWorklist.closed 3 [] [value] = false := by cbv
    cases actual with
    | empty impossible _ => rw [notEmpty] at impossible; cases impossible
    | skip _ impossible _ => rw [fresh] at impossible; cases impossible
    | admit _ _ rows rest =>
        have retained := rest.retains
        have first := retained.1 (SourceCurrentConjunctionEmptinessTable.keys SourceCurrentConjunctionRequirements.key [value])
          ⟨[value], _⟩ (by simp only [SourceCurrentConjunctionEmptinessTable.lookup, ite_true])
        intro empty
        rw [empty] at first
        cases first
  exact ⟨value, before, final, after, closed, rfl, positive_source.1, positive_source.2, actual, nonempty, table, annotation⟩

/-- A literal nonempty equality class constructs its projections over recursive and union children. -/
theorem constructed_live_tuple :
    ∃ (original : EdgeValue Nat Guard) (initial after : Physical) (rows : List (List (Value Nat Guard))),
      (match original.children[0]? with | some (Value.mu _ _ _ _) => True | _ => False) ∧
      (match original.children[1]? with | some (Value.union _ _ _ _) => True | _ => False) ∧
      Tuple [original] initial (some rows) after ∧ rows.length = 3 ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ guards initial.heap) after.heap := by
  let folded := SourceCurrentConjunctionEquality.fold [edge] operations
  let result : SourceEqualityConstraintAllocation.Value := match folded.1 with
    | .ok (some result) => result | _ => .contradiction
  have completed : folded.1 = .ok (some result) := by dsimp only [folded, result]; cbv
  have classes : SourceEqualityInheritedPayload.classes result.payload = some [[[0],[1]]] := by dsimp only [folded, result]; cbv
  have resident : InternedNestedProvenance.Edges heap [edge] := by
    intro selected member
    simpa only [List.mem_singleton.mp member] using edge_resident
  obtain ⟨rows, after, requirements, _effects, _ready⟩ := SourceCurrentConjunctionRequirements.complete
    (fun guard => guard ∈ guards heap) [edge] [[[0],[1]]] heap semantic initial_ready.costs
    (initial heap semantic.ready.semantic.1.normal.facts) resident edge_closed
    (by intro selected member; have same := List.mem_singleton.mp member; subst selected; rfl)
  have graph : Tuple [edge] before (some rows) ⟨after, folded.2⟩ := .live completed classes requirements
  have carrier := tuple_heap _ graph initial_ready.semantic initial_ready.costs resident edge_closed
    (initial heap semantic.ready.semantic.1.normal.facts)
  have length := requirements.length
  have arity : SourceCurrentConjunctionRequirements.arity [edge] = 2 := by cbv
  simp only [List.length_cons, List.length_nil, Nat.zero_add, arity] at length
  exact ⟨edge, before, ⟨after, folded.2⟩, rows, recursive_union.1, recursive_union.2, graph, length, carrier⟩
end MicroCFTA.GuardUniverseKernels

#print axioms MicroCFTA.GuardUniverseKernels.constructed_exploration
#check @MicroCFTA.GuardUniverseKernels.constructed_exploration
#print axioms MicroCFTA.GuardUniverseKernels.constructed_live_tuple
#check @MicroCFTA.GuardUniverseKernels.constructed_live_tuple
