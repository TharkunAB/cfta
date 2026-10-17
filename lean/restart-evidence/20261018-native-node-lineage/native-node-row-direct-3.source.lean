import MicroCFTA.SourceCurrentNativeReaderRowLineage

/-!
# Row and ordered-child lineage from returned native node cells

An actual returned ordinary node cell retains its captured compiler body.
The ordinary branch derives the literal row compiler trace from that body.
Final-reader history describes each surviving row and its historical child
call. No history at an internal active owner is required.
-/
namespace MicroCFTA.SourceCurrentNativeNodeRowLineage
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One captured node body retains its protected finish and the selected historical ordered child call. -/
def Lineage (reader : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Value Symbol Guard) (rowIndex : Nat) (row : EdgeValue Symbol Guard)
    (childIndex : Nat) (value : Value Symbol Guard) : Prop :=
  ∃ (before after : Checked width) (fuel : Nat),
    Good before ∧ NodeReady before.native.machine request ∧
    before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
    Trace fuel (.code (compileRows request.domain (nodeEdges request.left) (nodeEdges request.right)))
      before (.code (.pure result)) after ∧
    after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
    Trace 1 (.code (.finishNode handle result (.pure result))) after (.code (.pure result))
      {after with native := finishNode handle result after.native} ∧
    Grows before.native.machine.heap reader.native.machine.heap ∧
    Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
    (nodeEdges result)[rowIndex]? = some row ∧ row.children[childIndex]? = some value ∧
    ∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (edgeHandle : Nat)
      (leftChild rightChild : Value Symbol Guard) (callBefore callAfter : Checked width) (childFuel : Nat),
      (nodeEdges request.left)[leftIndex]? = some leftRow ∧
      (nodeEdges request.right)[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      SourceCurrentNativeEdgeWriterGrowth.Written (width := width) edgeHandle
        ⟨request.domain,leftRow,rightRow⟩ row reader.native.machine.heap ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
        leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[childIndex]? = some leftChild ∧ rightRow.children[childIndex]? = some rightChild ∧
      Good callBefore ∧ Good callAfter ∧
      Grows callBefore.native.machine.heap reader.native.machine.heap ∧
      Grows callAfter.native.machine.heap reader.native.machine.heap ∧
      Trace childFuel (.code (requestNode request.domain leftChild rightChild))
        callBefore (.code (.pure value)) callAfter

/-- A returned ordinary node cell derives its actual row compiler and full indexed child lineage. -/
theorem ordinary {reader : Checked width} (history : History reader)
    (handle : Nat) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (returned : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (leftEntry rightEntry : Interned InternedBinderProtocol.NodeKey) (leftRows rightRows : List (EdgeValue Symbol Guard))
    (leftDepth rightDepth : Nat) (leftFree rightFree : List InternedBinderProtocol.Reference)
    (left : request.left = .node leftEntry leftRows leftDepth leftFree)
    (right : request.right = .node rightEntry rightRows rightDepth rightFree)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (rowSelected : (nodeEdges result)[rowIndex]? = some row)
    (childIndex : Nat) (value : Value Symbol Guard) (childSelected : row.children[childIndex]? = some value) :
    Lineage reader handle request result rowIndex row childIndex value := by
  obtain ⟨before,after,fuel,good,ready,owner,body,ownerKept,finish,first,last,retained⟩ :=
    SourceCurrentNativeWriterReadyRetention.writers history handle request result returned
  have compiled : compileNode request = compileRows request.domain (nodeEdges request.left) (nodeEdges request.right) := by
    unfold compileNode
    simp only [selected]
    rw [left,right]
    rfl
  have rows : Trace fuel (.code (compileRows request.domain (nodeEdges request.left) (nodeEdges request.right)))
      before (.code (.pure result)) after := by
    rw [← compiled]
    exact body
  have child := SourceCurrentNativeReaderRowLineage.rows_child history request.domain
    (nodeEdges request.left) (nodeEdges request.right) fuel result good rows retained
    rowIndex row rowSelected childIndex value childSelected
  exact ⟨before,after,fuel,good,ready,owner,body,rows,ownerKept,finish,first,last,retained,rowSelected,childSelected,child⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem ready_unchanged {reader : Checked width}
    (request : NodeRequest Symbol Guard) (chosen : Native width Symbol Guard) (handle : Nat)
    (result : Value Symbol Guard)
    (selected : lookupNode width request reader.native = (.memoized handle,chosen))
    (stored : chosen.nodes.cells handle = some ⟨request,.returned result⟩) : chosen = reader.native := by
  cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simp only [lookupNode,requested,Prod.mk.injEq] at selected; cases selected.1
  | some key =>
      cases found : reader.native.nodes.table key with
      | some previous =>
          have same := Prod.mk.inj (by simpa only [lookupNode,requested,FlatMemoThunk.lookupOrInsert,found] using selected)
          exact same.2.symm
      | none =>
          have same := Prod.mk.inj (by simpa only [lookupNode,requested,FlatMemoThunk.lookupOrInsert,found] using selected)
          have handles : handle = reader.native.nodes.next := by cases same.1; rfl
          rw [← same.2,handles] at stored
          simp [Cache.put] at stored

/-- A literal ready lookup identifies the unchanged reader and the captured ordinary node's full lineage. -/
theorem warm {reader : Checked width} (history : History reader) (good : Good reader)
    (request : NodeRequest Symbol Guard) (chosen running : Native width Symbol Guard)
    (handle : Nat) (result : Value Symbol Guard) (ready : NodeReady reader.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request reader.native = (.memoized handle,chosen))
    (demanded : demandNode handle chosen = (.ready result,running))
    (leftEntry rightEntry : Interned InternedBinderProtocol.NodeKey) (leftRows rightRows : List (EdgeValue Symbol Guard))
    (leftDepth rightDepth : Nat) (leftFree rightFree : List InternedBinderProtocol.Reference)
    (left : request.left = .node leftEntry leftRows leftDepth leftFree)
    (right : request.right = .node rightEntry rightRows rightDepth rightFree)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (rowSelected : (nodeEdges result)[rowIndex]? = some row)
    (childIndex : Nat) (value : Value Symbol Guard) (childSelected : row.children[childIndex]? = some value) :
    chosen = reader.native ∧ running = reader.native ∧
      Lineage reader handle request result rowIndex row childIndex value := by
  have checked := SourceCurrentAllocatedNativePhysicalCache.node_ready request reader.native chosen running handle result
    good.native ready safe selected demanded
  have same := ready_unchanged request chosen handle result selected checked.1
  have returned : reader.native.nodes.cells handle = some ⟨request,.returned result⟩ := by
    simpa only [same] using checked.1
  exact ⟨same,checked.2.1.trans same,ordinary history handle request result returned
    leftEntry rightEntry leftRows rightRows leftDepth rightDepth leftFree rightFree left right branch
    rowIndex row rowSelected childIndex value childSelected⟩

end MicroCFTA.SourceCurrentNativeNodeRowLineage
