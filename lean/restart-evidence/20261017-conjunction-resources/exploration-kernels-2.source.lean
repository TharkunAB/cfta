import MicroCFTA.SourceCurrentConjunctionRowsResources
import MicroCFTA.SourceCurrentConjunctionWorklistResources
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

namespace MicroCFTA.ExplorationResourceIntegration
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


private def resource := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next
  (InternedValueMassHeap.initialBound heap)
private theorem fits : SourceCurrentMemoMergeResourceControl.Fits resource heap :=
  SourceCurrentMemoMergeResourceControl.initial heap _
    (InternedValueMassHeap.initial heap semantic.ready.semantic.1.normal.facts)
private theorem pending_widths : ∀ nodes ∈ [[value], [.reference .depth]], nodes.length ≤ resource := by
  intro nodes member
  have positive := fits.stored.positive
  rcases List.mem_cons.mp member with rfl | member
  · exact positive
  · have same : nodes = [.reference .depth] := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    cases same
    exact positive
private theorem pending_not_closed : ¬MergedColdReaderClosedInputs.ClosedValues [value, .reference .depth] := by
  intro allClosed
  have impossible := allClosed (.reference .depth) (List.mem_cons_of_mem _ List.mem_cons_self)
  cases impossible
private theorem open_skips (budget : Nat)
    (table : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Nat Guard))) :
    SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
      SourceCurrentConjunctionWorklist.closed budget table [.reference .depth] = true := by
  simp only [SourceCurrentConjunctionEmptinessTable.skip, SourceCurrentConjunctionWorklist.closed,
    List.all_cons, List.all_nil, Value.free, List.isEmpty_cons, Bool.false_and, Bool.not_false, Bool.or_true, Bool.true_or]

/-- Original source facts construct complete numeric rows over real recursive and union children. -/
theorem constructed_rows :
    raw.equalities = some [[[0], [1]]] ∧
    (match edge.children[0]? with | some (Value.mu _ _ _ _) => True | _ => False) ∧
    (match edge.children[1]? with | some (Value.union _ _ _ _) => True | _ => False) ∧
    ∃ rows after, SourceCurrentConjunctionRowsAllocation.Rows [value] before rows after ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧
      SourceCurrentConjunctionRowsAllocation.RowsReady after rows ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ guards heap) after.heap ∧
      SourceCurrentMemoMergeResourceControl.Fits
        (SourceCurrentConjunctionRowsResources.forecast (guards heap) 2 resource) after.heap ∧
      (∀ row ∈ rows, ∀ requirement ∈ row,
        requirement.length ≤ SourceCurrentConjunctionRowsResources.forecast (guards heap) 2 resource) ∧
      ∀ work reader,
        SourceCurrentConjunctionProjectionResources.workerFuel
          (SourceCurrentConjunctionTupleBounds.shapeThrough (guards heap) 2) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel
          (SourceCurrentConjunctionRowsResources.forecast (guards heap) 2 resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.rows work reader [value] before = .done rows after := by
  exact ⟨rfl, recursive_union.1, recursive_union.2,
    SourceCurrentConjunctionRowsResources.complete [value] before (guards heap) 2 resource initial_ready
      source_inputs (by intro original member; have same := List.mem_singleton.mp member; cases same; exact closed)
      fits (by decide) (initial heap semantic.ready.semantic.1.normal.facts)⟩

/-- Numeric exploration constructs its own admission graph and permits an open skipped suffix. -/
theorem constructed_exploration :
    ¬MergedColdReaderClosedInputs.ClosedValues [value, .reference .depth] ∧
    (∀ (budget : Nat) (table : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Nat Guard))),
      SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
      SourceCurrentConjunctionWorklist.closed budget table [.reference .depth] = true) ∧
    ∃ final after, Run 3 [] [[value], [.reference .depth]] before final after ∧
      final ≠ [] ∧ SourceCurrentConjunctionRowsAllocation.Effects before after ∧
      SourceCurrentConjunctionWorklist.TableReady after final ∧ final.length ≤ 3 ∧
      SourceCurrentMemoMergeResourceControl.Fits
        (SourceCurrentConjunctionWorklistResources.forecast (guards heap) 3 resource) after.heap ∧
      ∀ work reader, SourceCurrentConjunctionWorklistResources.workerFuel (guards heap) 3 resource ≤ work →
        SourceCurrentConjunctionWorklistResources.readerFuel (guards heap) 3 resource ≤ reader →
        SourceCurrentConjunctionWorker.explore work reader 3 [] [[value], [.reference .depth]] before = .done final after := by
  obtain ⟨final, after, actual, effects, table, length, finalFits, done⟩ :=
    SourceCurrentConjunctionWorklistResources.entered 3 [[value], [.reference .depth]] before resource
      initial_ready initial_pending fits pending_widths
  have nonempty : final ≠ [] := by
    have notEmpty : [value].any SourceCurrentConjunctionRequirements.isEmpty = false := by cbv
    have fresh : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
        SourceCurrentConjunctionWorklist.closed 3 [] [value] = false := by cbv
    cases actual with
    | empty impossible _ => rw [notEmpty] at impossible; cases impossible
    | skip _ impossible _ => rw [fresh] at impossible; cases impossible
    | @admit budget table nodes before requirements middle pending final after _ _ rows rest =>
        have retained := rest.retains
        have found : SourceCurrentConjunctionEmptinessTable.lookup SourceCurrentConjunctionRequirements.key
            (SourceCurrentConjunctionEmptinessTable.keys SourceCurrentConjunctionRequirements.key [value])
            [⟨[value], requirements⟩] = some ⟨[value], requirements⟩ := by
          simp [SourceCurrentConjunctionEmptinessTable.lookup]
        have first := retained.1 _ _ found
        intro empty
        rw [empty] at first
        cases first
  exact ⟨pending_not_closed, open_skips, final, after, actual, nonempty, effects, table, length, finalFits, done⟩
end MicroCFTA.ExplorationResourceIntegration

#check @MicroCFTA.ExplorationResourceIntegration.constructed_rows
#print axioms MicroCFTA.ExplorationResourceIntegration.constructed_rows
#check @MicroCFTA.ExplorationResourceIntegration.constructed_exploration
#print axioms MicroCFTA.ExplorationResourceIntegration.constructed_exploration
