import MicroCFTA.SourceCurrentNativeMuWriterSourceRows
import MicroCFTA.SourceCurrentNativeOriginExposure
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentDirectedClosure

/-!
# Literal and opaque source handoffs at actual native Mu writers

The selected generated-body row can occur below a stored Mu. Such a source
occurrence is not an observed row. This theorem separates a literal row at
one fixed reader from the first opaque Mu on its indexed union path. The
opaque case derives that Mu's actual publication and raw body callback.
It does not identify that callback with an earlier query operand.
-/
namespace MicroCFTA.SourceCurrentNativeMuSourceHandoff
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (current_inputs effects)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceEqualityNativeDemandMemo (Retained)
open SourceRecursiveIntersectionControl (identity pair decision)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentDirectedClosure (Closure)
open SourceCurrentNativeMuPublication (Publication)
open MergedFreshOrdinaryGraph (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard

private def UnionStep (first second : Node) : Prop :=
  ∃ entry members depth free index, first = .union entry members depth free ∧ members[index]? = some second

private theorem row_split {value : Node} {row : Edge} (part : RowAt value row) :
    Row value row ∨ ∃ entry body depth ordinary,
      Literal value (.mu entry body depth ordinary) ∧
      Closure UnionStep value (.mu entry body depth ordinary) ∧ RowAt body row := by
  induction part with
  | node found => exact .inl (.node (List.mem_of_getElem? found))
  | @union entry members depth free index value row found _ ih =>
      rcases ih with literal | ⟨muEntry,body,muDepth,ordinary,literal,path,inside⟩
      · exact .inl (.union (List.mem_of_getElem? found) literal)
      · exact .inr ⟨muEntry,body,muDepth,ordinary,.union (List.mem_of_getElem? found) literal,
          .step ⟨entry,members,depth,free,index,rfl,found⟩ path,inside⟩
  | mu part => exact .inr ⟨_,_,_,_,.mu _ _ _ _,.refl _,part⟩

private theorem literal_origin [DecidableEq (EdgeKey Symbol Guard)] (reader : Heap)
    {value : Node} {row : Edge} (part : Row value row) : Origin reader [value] row := by
  induction part with
  | node member => exact ⟨_,.seed (by simp),member⟩
  | union member _ ih => exact (MergedFreshOrdinaryGraph.origin_union reader _ _ _ _ _).mpr ⟨_,member,ih⟩

private theorem union_available (heap : Heap) {first last : Node}
    (path : Closure UnionStep first last) (available : Available heap first) : Available heap last := by
  induction path with
  | refl => exact available
  | step one _ ih =>
      obtain ⟨entry,members,depth,free,index,rfl,found⟩ := one
      exact ih (available.children _ (by simpa only [children] using List.mem_of_getElem? found))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A selected actual Mu return derives either a literal open-child writer or the first opaque Mu's actual publication. -/
theorem returned {reader : Checked width} (history : History reader)
    (publications : SourceCurrentNativeMuPublication.History empty reader.native.machine.heap)
    (request : NodeRequest Symbol Guard) (result : Node) (handle : Nat)
    (present : reader.native.nodes.cells handle = some ⟨request,.returned result⟩)
    (branch : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu)
    (rowIndex : Nat) (row : Edge) (selected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ (before after : Checked width) (fuel first second childFuel : Nat)
        (bodyValue : Node) (middle : Checked width) (heap : Heap) (original : Edge),
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second
      let entry := {before with native := advance before.native {before.native.machine with domains := entered.2}}
      let childRequest : NodeRequest Symbol Guard := ⟨entered.1,body request.left,body request.right⟩
      Good before ∧ NodeReady before.native.machine request ∧
      before.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Trace fuel (.code (compileNode request)) before (.code (.pure result)) after ∧
      identity request.left = some first ∧ identity request.right = some second ∧ fuel = childFuel + 2 ∧
      Good entry ∧ Trace childFuel (.code (requestNode childRequest.domain childRequest.left childRequest.right))
        entry (.code (.pure bodyValue)) middle ∧ Good middle ∧
      Available middle.native.machine.heap bodyValue ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue middle.native.machine.heap = .done result heap ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap := heap}} ∧
      after.native.nodes.cells handle = some ⟨request,.evaluating⟩ ∧
      Grows before.native.machine.heap reader.native.machine.heap ∧
      Grows after.native.machine.heap reader.native.machine.heap ∧ Retained after.native reader.native ∧
      SourceCurrentNativeQueryMuRowOrigins.OptionalOrigin (pair first second) bodyValue middle.native.machine.heap
        result heap reader.native.machine.heap rowIndex row ∧
      RowAt bodyValue original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
      (row = original ∨ ∃ lexical current next, Calls lexical original.children current row.children next) ∧
      ((Row bodyValue original ∧ Origin reader.native.machine.heap [bodyValue] original ∧
          ∃ leftCodec rightCodec key childHandle,
            IntersectionFlatMemoKey.input childRequest.left.referenceOf = some leftCodec ∧
            IntersectionFlatMemoKey.input childRequest.right.referenceOf = some rightCodec ∧
            SourceRecursiveIntersectionMemo.requestKey width childRequest.domain childRequest.left childRequest.right = some key ∧
            reader.native.nodes.cells childHandle = some ⟨childRequest,.returned bodyValue⟩ ∧
            SourceCurrentNativeWriterReadyRetention.Written (width := width) childHandle childRequest bodyValue reader.native) ∨
        ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
          Literal bodyValue event.candidate ∧
          Closure (fun first second : Node => ∃ entry members depth free index,
            first = .union entry members depth free ∧ members[index]? = some second) bodyValue event.candidate ∧
          RowAt event.body original ∧
          reader.native.machine.heap.nodeRecords event.key = some event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (SourceCurrentNativeMuPublication.History empty event.before) ∧
          Nonempty (SourceCurrentNativeMuPublication.History event.before event.afterDepth) ∧
          Nonempty (SourceCurrentNativeMuPublication.History event.afterDepth event.cut) ∧
          Nonempty (SourceCurrentNativeMuPublication.History event.allocated event.afterBody) ∧
          ∃ raw current,
            InternedFreshOrdinaryConstruction.build event.expression
              (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw current ∧
            run (withoutSelfReference (.interned event.entry.identity) raw) current = (event.body,event.afterBody)) := by
  obtain ⟨before,after,fuel,first,second,childFuel,bodyValue,middle,heap,good,ready,owner,actual,
    leftId,rightId,count,child,available,binder,final,kept,firstGrowth,lastGrowth,retained,optional,
    original,part,symbol,guard,arity,children⟩ :=
    SourceCurrentNativeMuWriterSourceRows.returned_mu history publications request result handle present branch rowIndex row selected
  let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
    request.left request.right first second
  let entry := {before with native := advance before.native {before.native.machine with domains := entered.2}}
  let childRequest : NodeRequest Symbol Guard := ⟨entered.1,body request.left,body request.right⟩
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    rcases branch with branch | branch | branch <;> simp only [compileNode,branch]
  have muActual := compiled ▸ actual
  have one := SourceCurrentAllocatedNativeMuSource.enter_prefix request before first second leftId rightId
  have reached := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
    (.code (compileMu request.domain request.left request.right)) before good (current_inputs muActual)
    (SourceCurrentAllocatedNativeCodeFields.compileMu_fields before.operations request.domain request.left request.right)
  rw [one] at reached
  have entryGood : Good entry := reached.1
  have middleGood := (effects child entryGood (by intro value; trivial)).1
  have middleRetained : Retained middle.native reader.native := by
    have next := SourceEqualityNativeDemandMemo.advance_retained middle.native {middle.native.machine with heap := heap}
    rw [final] at retained
    exact next.trans retained
  have forwarded := SourceCurrentNativeReferenceOrigins.forwarded history childRequest childFuel bodyValue entryGood child middleRetained
  refine ⟨before,after,fuel,first,second,childFuel,bodyValue,middle,heap,original,
    good,ready,owner,actual,leftId,rightId,count,entryGood,child,middleGood,available,binder,final,kept,
    firstGrowth,lastGrowth,retained,optional,part,symbol,guard,arity,children,?_⟩
  rcases row_split part with literal | ⟨muEntry,storedBody,depth,ordinary,literal,path,inside⟩
  · have origin := literal_origin reader.native.machine.heap literal
    obtain ⟨leftCodec,rightCodec,key,left,right,keyed⟩ := SourceCurrentNativeOriginExposure.keyable
      childRequest childFuel bodyValue child reader.native.machine.heap original origin
    rcases forwarded.2 with ⟨missing,_⟩ | ⟨childHandle,cell,written⟩
    · rw [keyed] at missing
      cases missing
    · exact .inl ⟨literal,origin,leftCodec,rightCodec,key,childHandle,left,right,keyed,cell,written⟩
  · have muAvailable := union_available middle.native.machine.heap path available
    have stored := muAvailable.resident muEntry rfl
    have middleGrowth : Grows middle.native.machine.heap reader.native.machine.heap := by
      rw [final] at lastGrowth
      exact lastGrowth
    have current := middleGrowth.nodeRecords _ _ stored
    obtain ⟨event,key,same,missing,prefix,depthHistory,ordinaryHistory,bodyHistory⟩ :=
      publications.from_empty muEntry.key muEntry storedBody depth ordinary current
    have equal : muEntry = event.entry ∧ storedBody = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary :=
      Value.mu.inj same
    obtain ⟨rfl,rfl,rfl,rfl⟩ := equal
    obtain ⟨rawOrdinary,afterOrdinary,rawBody,afterBody,_ordinaryDone,_ordinaryFilter,bodyDone,bodyFilter,
      _ordinaryGrowth,_bodyGrowth,_depthContext,_bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
    exact .inr ⟨event,literal,path,inside,current,missing,prefix,depthHistory,ordinaryHistory,bodyHistory,
      rawBody,afterBody,bodyDone,bodyFilter⟩

end MicroCFTA.SourceCurrentNativeMuSourceHandoff
