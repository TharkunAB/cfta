import MicroCFTA.SourceCurrentNativeNodeRowLineage
import MicroCFTA.SourceCurrentUnconstrainedGuardClosure
import MicroCFTA.InternedValueMass

/-!
# Positive ordinary native rows and their source children

The actual returned node cell supplies its earlier captured writer. A
non-Plain joined row has a non-Plain source row on at least one side.
Both source children have smaller mass than their respective operands.
Their actual paired request produces the selected output child.

The operands are the inputs of this ordinary native request. They need
not be initial outer inputs. Self, union, reference and Mu branches have
separate origin receipts. This theorem does not compose those receipts
or bound repeated outer calls.
-/
namespace MicroCFTA.SourceCurrentNativePositiveRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History Written)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
variable {width : Nat}
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem positive_side {handle : Nat} {request : EdgeRequest Symbol Guard}
    {row : EdgeValue Symbol Guard} {reader : State Symbol Guard}
    (written : Written (width := width) handle request row reader)
    (guard : row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
      request.left.entry.key.constraint request.right.entry.key.constraint)
    (positive : ¬ Plain row.entry.key.constraint) :
    ¬ Plain request.left.entry.key.constraint ∨ ¬ Plain request.right.entry.key.constraint := by
  obtain ⟨before,_,_,good,ready,_⟩ := written
  by_cases first : Plain request.left.entry.key.constraint
  · right
    intro second
    apply positive
    rw [guard]
    exact SourceCurrentUnconstrainedGuardClosure.conjoin_plain GuardStructuralOrder.le _ _
      (SourceEqualityGuardReadback.active (good.fields _ _ ready.2.1).1)
      (SourceEqualityGuardReadback.active (good.fields _ _ ready.2.2).1) first second
  · exact .inl first

/-- A positive actual ordinary result retains a positive source side and its smaller paired child. -/
theorem positive_child {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (returned : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (leftEntry rightEntry : Interned InternedBinderProtocol.NodeKey)
    (leftRows rightRows : List (EdgeValue Symbol Guard)) (leftDepth rightDepth : Nat)
    (leftFree rightFree : List InternedBinderProtocol.Reference)
    (left : request.left = .node leftEntry leftRows leftDepth leftFree)
    (right : request.right = .node rightEntry rightRows rightDepth rightFree)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard)
    (selected : (nodeEdges result)[rowIndex]? = some row)
    (positive : ¬ Plain row.entry.key.constraint)
    (childIndex : Nat) (value : Value Symbol Guard)
    (childSelected : row.children[childIndex]? = some value) :
    ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (edgeHandle : Nat)
      (leftChild rightChild : Value Symbol Guard) (before after : Checked width) (fuel : Nat),
      (nodeEdges request.left)[leftIndex]? = some leftRow ∧
      (nodeEdges request.right)[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      Written (width := width) edgeHandle ⟨request.domain,leftRow,rightRow⟩ row reader.native.machine.heap ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
        leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      (¬ Plain leftRow.entry.key.constraint ∨ ¬ Plain rightRow.entry.key.constraint) ∧
      leftRow.children[childIndex]? = some leftChild ∧ rightRow.children[childIndex]? = some rightChild ∧
      InternedValueMass.value leftChild < InternedValueMass.value request.left ∧
      InternedValueMass.value rightChild < InternedValueMass.value request.right ∧
      Good before ∧ Good after ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧
      Trace fuel (.code (requestNode request.domain leftChild rightChild)) before (.code (.pure value)) after := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,leftIndex,rightIndex,leftRow,rightRow,edgeHandle,
      leftChild,rightChild,before,after,fuel,leftFound,rightFound,symbols,written,symbol,guard,
      firstChild,secondChild,initial,final,firstGrowth,lastGrowth,actual⟩ :=
    SourceCurrentNativeNodeRowLineage.ordinary history handle request result returned
      leftEntry rightEntry leftRows rightRows leftDepth rightDepth leftFree rightFree left right branch
      rowIndex row selected childIndex value childSelected
  have firstMember : leftRow ∈ leftRows := by
    simpa only [left,nodeEdges] using List.mem_of_getElem? leftFound
  have secondMember : rightRow ∈ rightRows := by
    simpa only [right,nodeEdges] using List.mem_of_getElem? rightFound
  have firstMass : InternedValueMass.value leftChild < InternedValueMass.value request.left := by
    rw [left]
    exact InternedValueMass.node_child_lt leftEntry leftRows leftDepth leftFree
      leftRow firstMember leftChild (List.mem_of_getElem? firstChild)
  have secondMass : InternedValueMass.value rightChild < InternedValueMass.value request.right := by
    rw [right]
    exact InternedValueMass.node_child_lt rightEntry rightRows rightDepth rightFree
      rightRow secondMember rightChild (List.mem_of_getElem? secondChild)
  exact ⟨leftIndex,rightIndex,leftRow,rightRow,edgeHandle,leftChild,rightChild,before,after,fuel,
    leftFound,rightFound,symbols,written,symbol,guard,positive_side written guard positive,
    firstChild,secondChild,firstMass,secondMass,initial,final,firstGrowth,lastGrowth,actual⟩

end MicroCFTA.SourceCurrentNativePositiveRowOrigins
