import MicroCFTA.SourceCurrentNativeMuSourceHandoff
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
import MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.NativeMuHandoffKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand IntersectSchedule SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def base : Syntax Symbol Guard := .node [.mk ("base", .top) top []]
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  base, .binder false (.binder true (.union [base, .node [.mk ("recursive",.top) top [.var 0]]]))]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 130 := ⟨initial 130 machine,operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private theorem constructed : built = .done root heap := by cbv
private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression,base,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built,heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts,Cache.empty_valid⟩,semantic.ready,loaded.1,?_⟩
  intro key row found
  rw [guarded key row found]
  exact loaded.2.2
private theorem available : Available heap left ∧ Available heap right := by
  have source := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact source.children left (by cbv; exact .head _)
  · exact source.children right (by cbv; exact .tail _ (.head _))
private def selected : EdgeValue Symbol Guard := match left with
  | .node _ (row :: _) _ _ => row
  | _ => (run (makeEdge ("fallback",.top) top []) empty).1
private theorem selected_row : (nodeEdges left)[0]? = some selected := by cbv

noncomputable section
private def after : Checked 130 := (execute 64 control before).state
private theorem literal : execute 64 control before = .done left after := by cbv
private theorem warm : execute 2 control after = .done left after := by cbv
private theorem branch : SourceRecursiveIntersectionControl.decision request.domain.key left right = .rightMu := by cbv
private theorem closed_left : left.free = [] := by cbv
private theorem closed_right : right.free = [] := by cbv
private theorem nested_used : (match right with
    | .mu _ (.mu inner innerBody _ _) _ _ => .interned inner.identity ∈ innerBody.free
    | _ => False) := by cbv; exact .head _

private def Claim : Prop :=
  built = .done root heap ∧
  (match right with
    | .mu _ (.mu inner innerBody _ _) _ _ => .interned inner.identity ∈ innerBody.free
    | _ => False) ∧
  execute 64 control before = .done left after ∧ execute 2 control after = .done left after ∧
  ∃ fuel handle,
    SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel control before left after
      (fun final value => Available final.heap value) ∧
    after.native.nodes.cells handle = some ⟨request,.returned left⟩ ∧
    ∃ (captured middle : Checked 130) (count first second : Nat) (bodyValue : Value Symbol Guard)
        (original : EdgeValue Symbol Guard),
      let entered := SourceRecursiveIntersectionEnvironment.enter captured.native.machine.domains
        request.domain.key left right first second
      let entry := {captured with native := advance captured.native {captured.native.machine with domains := entered.2}}
      let child : NodeRequest Symbol Guard := ⟨entered.1,body left,body right⟩
      Good captured ∧ Good entry ∧ Good middle ∧
      Trace count (.code (requestNode child.domain child.left child.right)) entry (.code (.pure bodyValue)) middle ∧
      SourceCurrentStoredLiteralRowLineage.RowAt bodyValue original ∧
      selected.entry.key.symbol = original.entry.key.symbol ∧ selected.entry.key.constraint = original.entry.key.constraint ∧
      ((SourceCurrentLiteralRootParts.Row bodyValue original ∧
          MergedFreshOrdinaryGraph.Origin after.native.machine.heap [bodyValue] original ∧
          ∃ childHandle, after.native.nodes.cells childHandle = some ⟨child,.returned bodyValue⟩ ∧
            SourceCurrentNativeWriterReadyRetention.Written (width := 130) childHandle child bodyValue after.native) ∨
        ∃ event : SourceCurrentNativeMuPublication.Publication,
          SourceCurrentLiteralRootParts.Literal bodyValue event.candidate ∧
          SourceCurrentStoredLiteralRowLineage.RowAt event.body original ∧
          after.native.machine.heap.nodeRecords event.key = some event.candidate ∧
          ∃ raw current,
            InternedFreshOrdinaryConstruction.build event.expression
              (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw current ∧
            run (withoutSelfReference (.interned event.entry.identity) raw) current = (event.body,event.afterBody))
private theorem checked : Claim := by
  have facts := initial_good.native.machine.1
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have originalLeft := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent available.1 closed_left
  have originalRight := SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent available.2 closed_right
  obtain ⟨fuel,value,final,receipt,_,_,_,_,_,_,_,_⟩ :=
    SourceCurrentAllocatedNativeInitialInstructionBudget.initial 128 (fun _ _ => true) before initial_good semantic
      (SourceRecursiveIntersectionNative.idle_initial machine) left right originalLeft originalRight
      available.1 available.2 closed_left closed_right (by cbv) (by cbv) (by cbv)
  obtain ⟨rfl,rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique (fuel+1) 64 control
    before final after value left receipt.done literal
  have initialHistory : SourceCurrentNativeEdgeWriterGrowth.History before := .initial machine operations
  have initialPublications : SourceCurrentNativeMuPublication.History empty heap :=
    SourceCurrentNativeMuPublication.closed_history expression
  obtain ⟨reached,_good,_growth,origin⟩ :=
    SourceCurrentSharedLeafNativeLineage.request request fuel left initial_good initialHistory receipt.trace
  obtain ⟨handle,present,_⟩ := origin.returned closed_left closed_right
  obtain ⟨_,⟨published⟩⟩ := SourceCurrentNativePublicationTrace.from_history receipt.trace initial_good.heap.semantic initialPublications
  obtain ⟨captured,finished,bodyFuel,first,second,childFuel,bodyValue,middle,binderHeap,original,
    capturedGood,_ready,_owner,_actual,_leftId,_rightId,_count,entryGood,child,middleGood,_available,_binder,_final,
    _kept,_firstGrowth,_lastGrowth,_retained,_optional,part,symbol,guard,_arity,_children,source⟩ :=
    SourceCurrentNativeMuSourceHandoff.returned reached published request left handle present
      (.inr (.inr branch)) 0 selected selected_row
  refine ⟨constructed,nested_used,literal,warm,fuel,handle,receipt,present,
    captured,middle,childFuel,first,second,bodyValue,original,capturedGood,entryGood,middleGood,child,part,symbol,guard,?_⟩
  rcases source with ⟨literal,observed,leftCodec,rightCodec,key,childHandle,_left,_right,_keyed,cell,written⟩ |
      ⟨event,literal,_path,inside,cell,_missing,_earlier,_depth,_ordinary,_body,raw,current,called,filtered⟩
  · exact .inl ⟨literal,observed,childHandle,cell,written⟩
  · exact .inr ⟨event,literal,inside,cell,raw,current,called,filtered⟩

/-- A source-built nested used Mu query returns a row and reuses its actual captured open-child handoff on a warm call. -/
theorem nested_cold_warm :
  built = .done root heap ∧
  (match right with
    | .mu _ (.mu inner innerBody _ _) _ _ => .interned inner.identity ∈ innerBody.free
    | _ => False) ∧
  execute 64 control before = .done left after ∧ execute 2 control after = .done left after ∧
  ∃ fuel handle,
    SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel control before left after
      (fun final value => Available final.heap value) ∧
    after.native.nodes.cells handle = some ⟨request,.returned left⟩ ∧
    ∃ (captured middle : Checked 130) (count first second : Nat) (bodyValue : Value Symbol Guard)
        (original : EdgeValue Symbol Guard),
      let entered := SourceRecursiveIntersectionEnvironment.enter captured.native.machine.domains
        request.domain.key left right first second
      let entry := {captured with native := advance captured.native {captured.native.machine with domains := entered.2}}
      let child : NodeRequest Symbol Guard := ⟨entered.1,body left,body right⟩
      Good captured ∧ Good entry ∧ Good middle ∧
      Trace count (.code (requestNode child.domain child.left child.right)) entry (.code (.pure bodyValue)) middle ∧
      SourceCurrentStoredLiteralRowLineage.RowAt bodyValue original ∧
      selected.entry.key.symbol = original.entry.key.symbol ∧ selected.entry.key.constraint = original.entry.key.constraint ∧
      ((SourceCurrentLiteralRootParts.Row bodyValue original ∧
          MergedFreshOrdinaryGraph.Origin after.native.machine.heap [bodyValue] original ∧
          ∃ childHandle, after.native.nodes.cells childHandle = some ⟨child,.returned bodyValue⟩ ∧
            SourceCurrentNativeWriterReadyRetention.Written (width := 130) childHandle child bodyValue after.native) ∨
        ∃ event : SourceCurrentNativeMuPublication.Publication,
          SourceCurrentLiteralRootParts.Literal bodyValue event.candidate ∧
          SourceCurrentStoredLiteralRowLineage.RowAt event.body original ∧
          after.native.machine.heap.nodeRecords event.key = some event.candidate ∧
          ∃ raw current,
            InternedFreshOrdinaryConstruction.build event.expression
              (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw current ∧
            run (withoutSelfReference (.interned event.entry.identity) raw) current = (event.body,event.afterBody)) := checked
end
end MicroCFTA.NativeMuHandoffKernels
