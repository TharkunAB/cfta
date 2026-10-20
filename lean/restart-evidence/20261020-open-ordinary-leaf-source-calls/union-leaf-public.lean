import MicroCFTA.SourceCurrentBuildStructuralRowOrigins
import MicroCFTA.InternedFreshOrdinaryActiveOrigins

/-!
# Closed union leaves after actual outer normalization

The raw Depth callback builds a closed union and an open sibling. Outer
normalization flattens that closed union. Its whole Mu members then become
outer leaves although neither original member has that same leaf.
-/
namespace MicroCFTA.UnionClosedLeafNormalizationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryFacts (callback)
open InternedStoredSubstitution (leaves)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open InternedFreshOrdinaryActiveOrigins (Entered)
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option cbv.maxSteps 10000000
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool
local notation "Row" => EdgeValue Nat Bool

private def firstSource : Syntax Nat Bool := .binder false (.node [.mk 17 true []])
private def secondSource : Syntax Nat Bool := .binder false (.node [.mk 19 true []])
private def innerSource : Syntax Nat Bool := .union [firstSource,secondSource]
private def outerSource : Syntax Nat Bool := .union [innerSource,.var 0]
private def inputs : List Node := [.reference .depth]
private def outcomeValue (outcome : Outcome Nat Bool Node) : Node :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def firstRun := build firstSource inputs (empty : Heap)
private def firstMu : Node := outcomeValue firstRun
private def secondRun := build secondSource inputs firstRun.state
private def secondMu : Node := outcomeValue secondRun
private def innerRun := build innerSource inputs (empty : Heap)
private def innerValue : Node := outcomeValue innerRun
private def outerRun := build outerSource inputs (empty : Heap)
private def outerValue : Node := outcomeValue outerRun
private def row : Row := match firstMu with
  | .mu _ (.node _ (first :: _) _ _) _ _ => first
  | _ => (run (makeEdge 0 false []) (empty : Heap)).1

private theorem entered_context : Context (empty : Heap) inputs :=
  (SourceCurrentConstrainedCapSourceHistory.empty_context (Symbol := Nat) (Guard := Bool)).local
    .depth (InternedNestedProvenance.depth_available _)
private theorem entered : Entered false outerSource [] (empty : Heap) .depth (empty : Heap) := .depth
private theorem first_done : build firstSource inputs (empty : Heap) = .done firstMu firstRun.state := by cbv
private theorem second_done : build secondSource inputs firstRun.state = .done secondMu secondRun.state := by cbv
private theorem inner_done : build innerSource inputs (empty : Heap) = .done innerValue innerRun.state := by cbv
private theorem members_done : buildMany [innerSource,.var 0] inputs (empty : Heap) =
    .done [innerValue,.reference .depth] innerRun.state := by cbv
private theorem outer_done : build outerSource inputs (empty : Heap) = .done outerValue outerRun.state := by cbv
private theorem callback_done : callback outerSource [] .depth (empty : Heap) = .done innerValue outerRun.state := by cbv
private theorem inner_closed : innerValue.free = [] := by cbv
private theorem first_closed : firstMu.free = [] := by cbv
private theorem second_closed : secondMu.free = [] := by cbv
private theorem mu_witness (value : Node)
    (shape : match value with | .mu .. => True | _ => False) :
    ∃ entry body depth ordinary, value = .mu entry body depth ordinary := by
  cases value with
  | mu entry body depth ordinary => exact ⟨entry,body,depth,ordinary,rfl⟩
  | empty | reference | node | union => cases shape
private theorem first_shape : ∃ entry body depth ordinary, firstMu = .mu entry body depth ordinary :=
  mu_witness firstMu (by cbv)
private theorem second_shape : ∃ entry body depth ordinary, secondMu = .mu entry body depth ordinary :=
  mu_witness secondMu (by cbv)
private theorem inner_members : unionMembers innerValue = [firstMu,secondMu] := by cbv
private theorem distinct_mu : firstMu ≠ secondMu := by
  intro same
  have different : firstMu.referenceOf ≠ secondMu.referenceOf := by decide +kernel
  exact different (congrArg Value.referenceOf same)
private theorem outer_open : outerValue.free ≠ [] := by decide +kernel
private theorem inner_leaves : leaves innerValue = [innerValue] := by cbv
private theorem depth_leaves : leaves (.reference .depth : Node) = [.reference .depth] := by cbv
private theorem exposed_leaf : firstMu ∈ leaves outerValue := by
  cbv
  exact List.mem_cons_self
private theorem row_bearing : RowAt firstMu row := by
  cbv
  exact .mu (.node (index := 0) rfl)
private theorem missing_inner : firstMu ∉ leaves innerValue := by
  intro member
  have same : firstMu = innerValue := by simpa only [inner_leaves,List.mem_singleton] using member
  have different : firstMu.referenceOf ≠ innerValue.referenceOf := by decide +kernel
  exact different (congrArg Value.referenceOf same)
private theorem missing_depth : firstMu ∉ leaves (.reference .depth : Node) := by
  intro member
  have same : firstMu = .reference .depth := by simpa only [depth_leaves,List.mem_singleton] using member
  have different : firstMu.referenceOf ≠ (.reference .depth : Node).referenceOf := by decide +kernel
  exact different (congrArg Value.referenceOf same)
private theorem no_member_descent :
    ¬ ∀ leaf ∈ leaves outerValue, ∃ original ∈ [innerValue,.reference .depth], leaf ∈ leaves original := by
  intro alleged
  obtain ⟨original,member,inside⟩ := alleged firstMu exposed_leaf
  rcases List.mem_cons.mp member with same | last
  · subst original
    exact missing_inner inside
  · have same : original = .reference .depth := List.mem_singleton.mp last
    subst original
    exact missing_depth inside

private theorem checked_witness :
    Context (empty : Heap) inputs ∧
    Entered false outerSource [] (empty : Heap) .depth (empty : Heap) ∧
    build firstSource inputs (empty : Heap) = .done firstMu firstRun.state ∧
    build secondSource inputs firstRun.state = .done secondMu secondRun.state ∧
    build innerSource inputs (empty : Heap) = .done innerValue innerRun.state ∧
    buildMany [innerSource,.var 0] inputs (empty : Heap) = .done [innerValue,.reference .depth] innerRun.state ∧
    build outerSource inputs (empty : Heap) = .done outerValue outerRun.state ∧
    callback outerSource [] .depth (empty : Heap) = .done innerValue outerRun.state ∧
    innerValue.free = [] ∧ firstMu.free = [] ∧ secondMu.free = [] ∧
    (∃ entry body depth ordinary, firstMu = .mu entry body depth ordinary) ∧
    (∃ entry body depth ordinary, secondMu = .mu entry body depth ordinary) ∧
    unionMembers innerValue = [firstMu,secondMu] ∧ firstMu ≠ secondMu ∧
    outerValue.free ≠ [] ∧ leaves innerValue = [innerValue] ∧
    leaves (.reference .depth : Node) = [.reference .depth] ∧
    firstMu ∈ leaves outerValue ∧ RowAt firstMu row ∧
    firstMu ∉ leaves innerValue ∧ firstMu ∉ leaves (.reference .depth : Node) ∧
    ¬ ∀ leaf ∈ leaves outerValue, ∃ original ∈ [innerValue,.reference .depth], leaf ∈ leaves original := by
  exact ⟨entered_context,entered,first_done,second_done,inner_done,members_done,outer_done,callback_done,
    inner_closed,first_closed,second_closed,first_shape,second_shape,inner_members,distinct_mu,outer_open,
    inner_leaves,depth_leaves,exposed_leaf,row_bearing,missing_inner,missing_depth,no_member_descent⟩

/-- Actual open outer normalization exposes a row-bearing Mu absent from every original member's leaves. -/
theorem closed_union_flattening :
    Context (empty : Heap) inputs ∧
    Entered false outerSource [] (empty : Heap) .depth (empty : Heap) ∧
    build firstSource inputs (empty : Heap) = .done firstMu firstRun.state ∧
    build secondSource inputs firstRun.state = .done secondMu secondRun.state ∧
    build innerSource inputs (empty : Heap) = .done innerValue innerRun.state ∧
    buildMany [innerSource,.var 0] inputs (empty : Heap) = .done [innerValue,.reference .depth] innerRun.state ∧
    build outerSource inputs (empty : Heap) = .done outerValue outerRun.state ∧
    callback outerSource [] .depth (empty : Heap) = .done innerValue outerRun.state ∧
    innerValue.free = [] ∧ firstMu.free = [] ∧ secondMu.free = [] ∧
    (∃ entry body depth ordinary, firstMu = .mu entry body depth ordinary) ∧
    (∃ entry body depth ordinary, secondMu = .mu entry body depth ordinary) ∧
    unionMembers innerValue = [firstMu,secondMu] ∧ firstMu ≠ secondMu ∧
    outerValue.free ≠ [] ∧ leaves innerValue = [innerValue] ∧
    leaves (.reference .depth : Node) = [.reference .depth] ∧
    firstMu ∈ leaves outerValue ∧ RowAt firstMu row ∧
    firstMu ∉ leaves innerValue ∧ firstMu ∉ leaves (.reference .depth : Node) ∧
    ¬ ∀ leaf ∈ leaves outerValue, ∃ original ∈ [innerValue,.reference .depth], leaf ∈ leaves original := checked_witness

end MicroCFTA.UnionClosedLeafNormalizationKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.UnionClosedLeafNormalizationKernels.closed_union_flattening
#print MicroCFTA.UnionClosedLeafNormalizationKernels.closed_union_flattening
#print axioms MicroCFTA.UnionClosedLeafNormalizationKernels.closed_union_flattening
