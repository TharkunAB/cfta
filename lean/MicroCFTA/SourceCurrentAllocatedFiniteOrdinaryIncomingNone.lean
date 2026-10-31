import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored

set_option autoImplicit false

/-!
# Actual ordinary incoming writes into an unassigned slot

The None branch retains the caller and native Stored at every supplied fuel.
A successful representative read supplies the actual target slot.
Empty rejection returns no Core row. Its write prefix remains explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryIncomingNone
open InternedConstructorTemplates InternedProbeProvenance
open EnumerationState
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable {EnumGuard : Type} {width : Nat}
local instance noneMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation
variable [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual None branch stores the physical incoming handle and retains its current height cap. -/
theorem none_result (heightBound : Nat) (checkEmpty : Bool)
    (r n p h uv : Nat) (found : UnionFind.Result)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard) (incoming : Node)
    (incomingScs oldScs : List EnumerationState.Suspended) (queries : Queries)
    (ready : SourceCurrentConjunctionClassScan.Ready beforeCaller.checked)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (domain : NodeDomain incoming) (height : MergedOrdinaryHeight.height incoming ≤ heightBound)
    (stored : Stored beforeCaller.checked.native)
    (reading : UnionFind.findRoot r before.representatives uv = some found)
    (slot : before.values[found.representative]? = some (.unenumerated none oldScs)) :
    ∃ handle, ∃ after : EnumerationState.State Symbol EnumGuard,
      SourcePruningEnumerationNodes.encodeNode incoming = some handle ∧
      SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap handle = some incoming ∧
      NodeDomain incoming ∧ MergedOrdinaryHeight.height incoming ≤ heightBound ∧
      let read : EnumerationState.State Symbol EnumGuard := {before with representatives := found.forest}
      ExceptT.run ((do
        setValue found.representative (.unenumerated (some handle) (incomingScs ++ oldScs))
        inheritAncestry found.representative) read) = [.ok ((), after)] ∧
      SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
          beforeCaller before uv incoming incomingScs queries =
        (.ok (some (if incoming = .empty then [] else [.ok ((), after)])), beforeCaller, queries, read) ∧
      after = {read with
        values := read.values.set found.representative (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = found.representative then
          (read.expansionAncestry ++ read.recursionAncestry found.representative).eraseDups
          else read.recursionAncestry other} ∧
      after.values[found.representative]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      Stored (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
        beforeCaller before uv incoming incomingScs queries).2.1.checked.native := by
  obtain ⟨handle, encoded, decoded⟩ := SourcePruningEnumerationNodes.available_readback
    beforeCaller.checked.native.machine.heap incoming ready.semantic.ready.semantic.1.normal.facts.coherent available closed
  have inside : found.representative < before.values.length :=
    (List.getElem?_eq_some_iff.mp slot).elim (fun bound _value => bound)
  let read : EnumerationState.State Symbol EnumGuard := {before with representatives := found.forest}
  let after : EnumerationState.State Symbol EnumGuard := {read with
    values := read.values.set found.representative (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = found.representative then
      (read.expansionAncestry ++ read.recursionAncestry found.representative).eraseDups
      else read.recursionAncestry other}
  have raw : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      found.representative handle incomingScs oldScs incoming read) =
      (if incoming = .empty then [] else [.ok ((), after)]) := by
    cases incoming with
    | empty => simp only [↓reduceIte]; rfl
    | reference name => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | node entry edges depth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | union entry members depth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | mu entry body depthShape ordinaryShape => simp only [reduceCtorEq, ↓reduceIte]; rfl
  have actual : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      beforeCaller before uv incoming incomingScs queries =
      (.ok (some (if incoming = .empty then [] else [.ok ((), after)])), beforeCaller, queries, read) := by
    simp only [SourcePruningEnumerationIncomingNode.run, reading, slot, encoded]
    change (Except.ok (some (ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      found.representative handle incomingScs oldScs incoming read))), beforeCaller, queries, read) = _
    rw [raw]
  refine ⟨handle, after, encoded, decoded, domain, height, rfl, actual, rfl, ?_, ?_⟩
  · exact List.getElem?_set_self inside
  · rw [actual]
    exact stored

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryIncomingNone
