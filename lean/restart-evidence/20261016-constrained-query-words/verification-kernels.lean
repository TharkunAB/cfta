import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification
namespace FiniteOrdinaryOuterVerificationKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Two supplied actual read schedules derive both checks and their composed law without any range premise. -/
theorem two_actual_node_reads
    {inventory : Inventory} {budget : Nat} {request : NodeRequest} {before middle after : Caller width}
    {first last : Node} {memos intermediate final : Memos}
    {one : NodeCall budget request before first middle}
    {two : NodeCall budget ⟨request.inherited, first⟩ middle last after}
    (firstReads : NodeCallReads formulas solver one memos intermediate)
    (secondReads : NodeCallReads formulas solver two intermediate final)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) :
    Checks (nodeCallTrace one) ∧ Checks (nodeCallTrace two) ∧
      ∃ next, Post formulas solver next before after final ∧ Available after.checked.native.machine.heap last ∧
        Stored after ∧ NodeNarrow request.value last ∧ SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request last := by
  obtain ⟨firstChecks, firstInventory, firstPost, firstAvailable, firstStored, firstNarrow, firstLaw⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver firstReads inventory initial
      inherited available domain stored
  obtain ⟨secondChecks, next, secondPost, lastAvailable, lastStored, lastNarrow, lastLaw⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver secondReads firstInventory firstPost.context
      (inherited.grows firstPost.effects.grows.constraint_growth) firstAvailable firstNarrow.1 firstStored
  refine ⟨firstChecks, secondChecks, next, firstPost.trans secondPost, lastAvailable, lastStored,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.node_trans firstNarrow lastNarrow, ?_⟩
  intro ambient term
  exact ⟨fun accepted => (firstLaw ambient term).1 ((lastLaw ambient term).1 accepted),
    fun satisfied => ((lastLaw ambient term).2 satisfied).trans ((firstLaw ambient term).2 satisfied)⟩

/-- Actual row reads verify the literal ordinary-node reconstruction without caller-supplied checks. -/
theorem rows_rebuild_actual_node
    {inventory : Inventory} {budget : Nat} {inherited : SourceEqualityConstraintAllocation.Value}
    {entry : Interned InternedBinderProtocol.NodeKey} {edges results : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} {before middle : Caller width}
    {memos final : Memos} {actualRows : Rows budget inherited edges before results middle}
    (reads : RowsReads formulas solver actualRows memos final)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Available before.checked.native.machine.heap (.node entry edges depth free))
    (domain : DNode (.node entry edges depth free)) (stored : Stored before) :
    let result := (SourceCurrentAllocatedRawRebuild.modify (.node entry edges depth free) edges results middle.checked).1
    let after := advance middle (SourceCurrentAllocatedRawRebuild.modify (.node entry edges depth free) edges results middle.checked).2
      middle.fourth middle.merge
    ∃ actual : NodeBody budget ⟨inherited, .node entry edges depth free⟩ before result after,
      NodeBodyReads formulas solver actual memos final ∧ Checks (nodeBodyTrace actual) ∧
      ∃ next, Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ NodeNarrow (.node entry edges depth free) result ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver ⟨inherited, .node entry edges depth free⟩ result := by
  let actual := NodeBody.ordinary (entry := entry) (depth := depth) (free := free) actualRows
  have actualReads : NodeBodyReads formulas solver actual memos final := .ordinary reads
  have result := SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_body formulas solver actualReads inventory initial
    inheritedReady available domain stored
  exact ⟨actual, actualReads, result⟩
end FiniteOrdinaryOuterVerificationKernels
#print axioms FiniteOrdinaryOuterVerificationKernels.two_actual_node_reads
#check @FiniteOrdinaryOuterVerificationKernels.two_actual_node_reads
#print axioms FiniteOrdinaryOuterVerificationKernels.rows_rebuild_actual_node
#check @FiniteOrdinaryOuterVerificationKernels.rows_rebuild_actual_node
