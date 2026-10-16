import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile
import MicroCFTA.SourceEqualityNativeCheckedCode

/-!
# Static Work budgets for a complete ordinary query expansion

The scheme fixes row and arity limits on the original operands.
Each row-pair expansion includes all child requests and one constructor.
Continuations admit arbitrary returned values at a fixed budget.
No cache uniqueness or successful execution premise is used.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open MergedOrdinaryHeight (height edgeHeight edgesHeight)
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {Symbol Guard A : Type}

/-- Node calls retain the literal empty domain and both original uniform profiles. -/
def NodeInputs (rows arity : Nat) (request : NodeRequest Symbol Guard) : Prop :=
  request.domain = emptyDomain ∧ SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape rows arity request.left ∧ SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape rows arity request.right

/-- Edge calls retain the literal empty domain and both original uniform profiles. -/
def EdgeInputs (rows arity : Nat) (request : EdgeRequest Symbol Guard) : Prop :=
  request.domain = emptyDomain ∧ SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape rows arity request.left ∧ SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape rows arity request.right

/-- The whole node expansion uses the larger original operand height. -/
def nodeCost (rows arity : Nat) (request : NodeRequest Symbol Guard) : Nat :=
  nodeBudget rows arity (max (height request.left) (height request.right))

/-- The whole edge expansion uses the larger original child height. -/
def edgeCost (rows arity : Nat) (request : EdgeRequest Symbol Guard) : Nat :=
  edgeBudget rows arity (max (edgeHeight request.left) (edgeHeight request.right))

/-- Recursive costs depend only on the fixed original operand profile. -/
def scheme (rows arity : Nat) : Scheme Symbol Guard :=
  ⟨NodeInputs rows arity, EdgeInputs rows arity, nodeCost rows arity, edgeCost rows arity⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One node request reserves its full expansion and a zero-cost return. -/
theorem request_node (rows arity : Nat) (request : NodeRequest Symbol Guard) (inputs : NodeInputs rows arity request) :
    Bound (scheme rows arity) (requestNode request.domain request.left request.right) (nodeCost rows arity request) := by
  simpa only [requestNode, Nat.add_zero, scheme] using Bound.node (scheme := scheme rows arity) inputs
    (fun value => Bound.pure (scheme rows arity) value 0)

/-- One edge request reserves its full expansion and a zero-cost return. -/
theorem request_edge (rows arity : Nat) (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs rows arity request) :
    Bound (scheme rows arity) (requestEdge request.domain request.left request.right) (edgeCost rows arity request) := by
  simpa only [requestEdge, Nat.add_zero, scheme] using Bound.edge (scheme := scheme rows arity) inputs
    (fun value => Bound.pure (scheme rows arity) value 0)

/-- The joined row calls fit the whole next node layer, including its constructor. -/
theorem rows_bound [DecidableEq Symbol] (rows arity : Nat) (left right : List (EdgeValue Symbol Guard))
    (leftRows : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape rows arity left) (rightRows : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape rows arity right)
    (leftLength : left.length ≤ rows) (rightLength : right.length ≤ rows) :
    Bound (scheme rows arity) (compileRows emptyDomain left right)
      (nodeBudget rows arity (max (edgesHeight left) (edgesHeight right) + 1)) := by
  let limit := max (edgesHeight left) (edgesHeight right)
  have calls : ∀ pair ∈ pairs left right,
      Bound (scheme rows arity) (requestEdge emptyDomain pair.1 pair.2) (edgeBudget rows arity limit) := by
    intro pair member
    have inside := (pairs_member left right pair).mp member
    have bounded : max (edgeHeight pair.1) (edgeHeight pair.2) ≤ limit := by
      apply Nat.max_le.mpr
      exact ⟨Nat.le_trans ((MergedOrdinaryHeight.edgesHeight_le _ _).mp (Nat.le_refl _) _ inside.1) (Nat.le_max_left _ _),
        Nat.le_trans ((MergedOrdinaryHeight.edgesHeight_le _ _).mp (Nat.le_refl _) _ inside.2.1) (Nat.le_max_right _ _)⟩
    exact (request_edge rows arity ⟨emptyDomain, pair.1, pair.2⟩
      ⟨rfl, SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape.member left leftRows pair.1 inside.1,
        SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape.member right rightRows pair.2 inside.2.1⟩).weaken (edge_mono rows arity bounded)
  have walked := Bound.walk (scheme := scheme rows arity)
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge emptyDomain pair.1 pair.2)
    (pairs left right) (edgeBudget rows arity limit) calls
  have built : ∀ values : List (EdgeValue Symbol Guard), Bound (scheme rows arity) (.work (makeNode values) .pure) 1 := by
    intro values
    simpa only [Nat.add_zero] using Bound.work_makeNode (scheme := scheme rows arity) values
      (fun value => Bound.pure (scheme rows arity) value 0)
  have lengthBound : (pairs left right).length ≤ rows * rows :=
    Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.pairs_length_le left right) (Nat.mul_le_mul leftLength rightLength)
  have total := walked.bind built
  apply total.weaken
  rw [node_step]
  have product := Nat.mul_le_mul_left (edgeBudget rows arity limit) lengthBound
  simpa only [Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_right product 1

/-- The actual node dispatcher uses at most its whole expansion budget. -/
theorem node_bound [DecidableEq Symbol] (rows arity : Nat) (request : NodeRequest Symbol Guard)
    (inputs : NodeInputs rows arity request) :
    Bound (scheme rows arity) (compileNode request) (nodeCost rows arity request) := by
  rcases request with ⟨domain, left, right⟩
  rcases inputs with ⟨rfl, leftShape, rightShape⟩
  by_cases emptyCase : SourceRecursiveIntersectionControl.hasEmpty left right = true
  · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, ite_true, Bound]
  · have resetCase : SourceRecursiveIntersectionControl.reset (emptyDomain).key left right = false := by
      simp [SourceRecursiveIntersectionControl.reset, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey]
    by_cases selfCase : SourceRecursiveIntersectionControl.closedSelf left right = true
    · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase,
        Bool.false_eq_true, ite_false, ite_true, Bound]
    · by_cases swapCase : SourceRecursiveIntersectionControl.greater left right = true
      · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase,
          swapCase, Bool.false_eq_true, ite_false, ite_true]
        simpa only [nodeCost, Nat.max_comm] using
          request_node rows arity ⟨emptyDomain, right, left⟩ ⟨rfl, rightShape, leftShape⟩
      · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase,
          swapCase, Bool.false_eq_true, ite_false]
        have firstDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain left leftShape
        have secondDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain right rightShape
        cases firstDomain with
        | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Bound]
        | @ordinary left first leftDepth leftFree leftRows =>
            cases secondDomain with
            | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Bound]
            | @ordinary right second rightDepth rightFree rightRows =>
                simpa only [SourceRecursiveIntersectionControl.identity, IntersectionEmptyDomain.emptyDomain,
                  IntersectionEmptyDomain.emptyKey, List.not_mem_nil, Bool.false_eq_true, ite_false,
                  SourceRecursiveIntersectionControl.payload, nodeCost, height, Nat.add_max_add_right] using
                  rows_bound rows arity left right leftShape.2 rightShape.2 leftShape.1 rightShape.1

local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "SourceEdge" => EdgeValue SourceSymbol SourceGuard

/-- The exact child zip reserves every child expansion and the final raw edge constructor. -/
theorem children_bound [DecidableEq (EdgeKey SourceSymbol SourceGuard)] (rows arity : Nat)
    (request : EdgeRequest SourceSymbol SourceGuard) (inputs : EdgeInputs rows arity request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) :
    Bound (scheme rows arity) (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)
      (edgeCost rows arity request) := by
  let limit := max (edgeHeight request.left) (edgeHeight request.right)
  have calls : ∀ pair ∈ request.left.children.zip request.right.children,
      Bound (scheme rows arity) (requestNode request.domain pair.1 pair.2) (nodeBudget rows arity limit) := by
    intro pair member
    have inside := List.of_mem_zip member
    have bounded : max (height pair.1) (height pair.2) ≤ limit := by
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge _ _ inside.1) (Nat.le_max_left _ _),
          Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge _ _ inside.2) (Nat.le_max_right _ _)⟩
    exact (request_node rows arity ⟨request.domain, pair.1, pair.2⟩
      ⟨inputs.1, SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.member _
        (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children _ inputs.2.1) _ inside.1,
        SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.member _
          (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children _ inputs.2.2) _ inside.2⟩).weaken
        (node_mono rows arity bounded)
  have walked := Bound.walk (scheme := scheme rows arity)
    (fun pair => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) (nodeBudget rows arity limit) calls
  have built : ∀ values, Bound (scheme rows arity)
      (.work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure) 1 := by
    intro values
    simpa only [Nat.add_zero] using Bound.work_makeEdge (scheme := scheme rows arity) request.left.entry.key.symbol
      (SourceEqualityConjoinAllocation.readback combined) values (fun value => Bound.pure (scheme rows arity) value 0)
  have total := walked.bind built
  apply total.weaken
  have lengthBound : (request.left.children.zip request.right.children).length ≤ arity := by
    rw [List.length_zip]
    exact Nat.le_trans (Nat.min_le_left _ _) (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.arity _ inputs.2.1)
  have product := Nat.mul_le_mul_left (nodeBudget rows arity limit) lengthBound
  simpa only [edgeCost, edgeBudget, Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_right product 1

/-- A rejected edge reserves only its literal sentinel constructor. -/
theorem sentinel_bound [DecidableEq (EdgeKey SourceSymbol SourceGuard)] (rows arity : Nat)
    (request : EdgeRequest SourceSymbol SourceGuard) :
    Bound (scheme rows arity) (SourceEqualityNativeCheckedCode.sentinel request.left) (edgeCost rows arity request) := by
  have built : Bound (scheme rows arity) (SourceEqualityNativeCheckedCode.sentinel request.left) 1 := by
    simpa only [SourceEqualityNativeCheckedCode.sentinel, Nat.add_zero] using
      Bound.work_makeEdge (scheme := scheme rows arity) request.left.entry.key.symbol
        SourceEqualityConstraintConstructors.top [.empty] (fun value => Bound.pure (scheme rows arity) value 0)
  exact built.weaken (edge_positive rows arity _)

/-- Every actual checked edge-body yield fits its whole expansion and unchanged continuation budget. -/
theorem body_bound [DecidableEq (EdgeKey SourceSymbol SourceGuard)] {width : Nat} {Output : Type}
    (rows arity : Nat) (request : EdgeRequest SourceSymbol SourceGuard) (inputs : EdgeInputs rows arity request)
    (resume : SourceEdge → Code SourceSymbol SourceGuard Output)
    (before after : SourceEqualityNativeDemand.State width) (next : SourceEqualityNativeDemand.Control Output) (tail : Nat)
    (continuation : ∀ value, Bound (scheme rows arity) (resume value) tail)
    (yielded : SourceEqualityNativeDemand.body request resume before = .yielded next after) :
    ControlBound (scheme rows arity) next (edgeCost rows arity request + tail) := by
  have bindCode : ∀ code, Bound (scheme rows arity) code (edgeCost rows arity request) →
      ControlBound (scheme rows arity) (.code (code.bind resume)) (edgeCost rows arity request + tail) :=
    fun _ bound => bound.bind continuation
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [SourceEqualityNativeDemand.sentinel] at yielded
    cases yielded
    exact bindCode _ (sentinel_bound rows arity request)
  · split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact bindCode _ (sentinel_bound rows arity request)
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact bindCode _ (sentinel_bound rows arity request)
        · cases yielded
          exact bindCode _ (children_bound rows arity request inputs _)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile
