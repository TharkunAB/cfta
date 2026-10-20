import MicroCFTA.SourceCurrentNativeOriginalCapturedMuRows
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# Actual generated Mu with a shared initial inner capture

This calculation checks a new union-body source family.
The actual native generator must create a used outer full Mu.
The candidate shared inner Mu remains an initial leaf capture.
-/
noncomputable section
namespace MicroCFTA.GeneratedRowCaptureBackedgeFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentLiteralRootParts (Row)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeForwardLineage (Forwarded)
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
set_option maxHeartbeats 5000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 2048
set_option cbv.maxSteps 100000000
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def concreteWord (n : Nat) : BitVec 1024 :=
  if h : n < 1024 then BitVec.ofNatLT n (Nat.lt_of_lt_of_le h (by decide : 1024 ≤ 2^1024))
  else BitVec.ofNat 1024 n
private theorem word_small (n : Nat) : BitVec.ofNat 1024 n = concreteWord n := by
  unfold concreteWord
  split
  · apply BitVec.eq_of_toNat_eq
    change n % 2^1024 = n
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by assumption) (by decide : 1024 ≤ 2^1024))
  · rfl
attribute [local cbv_eval] word_small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def inner (label : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("innerRec",.top) top [.var 0],.mk (label,.top) top []])
private def recursive (label innerLabel : String) : Syntax Symbol Guard :=
  .binder false (.union [.node [.mk ("outerRec",.top) top [.var 0],.mk (label,.top) top []],inner innerLabel])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("pair",.top) top [recursive "outerLeft" "tag17",recursive "outerRight" "tag17"]]
private def built := InternedFreshOrdinaryConstruction.build expression [] (empty : Heap)
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def allocatedOps := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def before : Checked 1024 := ⟨initial 1024 machine,allocatedOps⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain request.left request.right)
private def outerPair := SourceRecursiveIntersectionControl.pair
  ((SourceRecursiveIntersectionControl.identity left).getD 0) ((SourceRecursiveIntersectionControl.identity right).getD 0)
private def locate : Nat → Nat → Control Node → Checked 1024 → Nat
  | 0, elapsed, _, _ => elapsed
  | remaining+1, elapsed, input, state =>
      match input with
      | .code (.optionalBinder pair _ _) =>
          match pair == outerPair with
          | true => elapsed
          | false => match step input state with
              | .yielded next after => locate remaining (elapsed+1) next after
              | _ => elapsed
      | _ => match step input state with
          | .yielded next after => locate remaining (elapsed+1) next after
          | _ => elapsed
private def fuel := locate 256 0 control before
private def outerRun := execute fuel control before
private def current : Checked 1024 := outerRun.state
private def bodyOf : Outcome 1024 Node → Node
  | .yielded (.code (.optionalBinder _ bodyValue _)) _ => bodyValue | _ => .empty
private def nextOf : Outcome 1024 Node → (Node → Code Symbol Guard Node)
  | .yielded (.code (.optionalBinder _ _ next)) _ => next | _ => .pure
private def optionalTag : Outcome 1024 Node → (Nat × Nat) → Prop
  | .yielded (.code (.optionalBinder pair _ _)) _,expected => pair = expected
  | _,_ => False
private theorem optional_rebuild (observation : Outcome 1024 Node) (expected : Nat × Nat)
    (tag : optionalTag observation expected) :
    observation = .yielded (.code (.optionalBinder expected (bodyOf observation) (nextOf observation))) observation.state := by
  cases observation with
  | yielded reached state =>
      cases reached with
      | edgeBody => cases tag
      | code code => cases code <;> simp_all [optionalTag,bodyOf,nextOf,Outcome.state]
  | done | failed | constraintError | blocked => cases tag
private def siteBody : Node := bodyOf outerRun
private def siteNext : Node → Code Symbol Guard Node := nextOf outerRun
private def muLeaf : Node → Bool := fun value => match value with | .mu .. => true | _ => false
private def captureIndex : Nat := (leaves siteBody).findIdx muLeaf
private def captured : Node := (leaves siteBody)[captureIndex]?.getD .empty
private def entry : Interned InternedBinderProtocol.NodeKey := match captured with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def stored : Node := match captured with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def depth : Node := match captured with | .mu _ _ probe _ => probe | _ => .empty
private def ordinary : Node := match captured with | .mu _ _ _ probe => probe | _ => .empty
private theorem built_done : built = .done root heap := by cbv
private theorem actual_tag : optionalTag outerRun outerPair := by cbv
private theorem actual_prefix : outerRun = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current :=
  optional_rebuild outerRun outerPair actual_tag
private theorem found : (leaves siteBody)[captureIndex]? = some (.mu entry stored depth ordinary) := by cbv
private theorem initial_capture : heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free := by
  constructor
  · cbv
  constructor
  · cbv
  · cbv
    exact List.mem_cons_self
private theorem bounded : 0 < fuel ∧ fuel < 256 := by constructor <;> cbv

private def generatedRun := SourceRecursiveIntersectionMaybeMu.maybeMu outerPair siteBody current.native.machine.heap
private def generated : Node := match generatedRun with | .done value _ => value | .pending .. => .empty
private def generatedHeap : Heap := generatedRun.state
private def generatedEntry : Interned InternedBinderProtocol.NodeKey := match generated with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def generatedBody : Node := match generated with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def generatedDepth : Node := match generated with | .mu _ _ probe _ => probe | _ => .empty
private def generatedOrdinary : Node := match generated with | .mu _ _ _ probe => probe | _ => .empty
private theorem generated_done : generatedRun = .done generated generatedHeap := by cbv
private theorem generated_shape : generated = .mu generatedEntry generatedBody generatedDepth generatedOrdinary := by cbv
private theorem generated_new : current.native.machine.heap.nodeRecords generatedEntry.key = none ∧
    generatedHeap.nodeRecords generatedEntry.key = some generated := by constructor <;> cbv
private theorem generated_used : Reference.interned generatedEntry.identity ∈ generatedBody.free := by
  cbv
  exact List.mem_cons_self
private theorem capture_index_small : captureIndex = 0 ∨ captureIndex = 1 := by cbv; decide

end MicroCFTA.GeneratedRowCaptureBackedgeFixture
