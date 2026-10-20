import MicroCFTA.SourceCurrentNativeOriginalCapturedMuRows
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceEqualityNormalizationReceipt
import Lean.Elab.Tactic.Conv

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
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 2048
set_option cbv.maxSteps 100000000
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def concreteWord (n : Nat) : BitVec 1024 :=
  BitVec.ofNatLT (n % 2^1024) (Nat.mod_lt _ (Nat.two_pow_pos 1024))
private theorem word_small (n : Nat) : BitVec.ofNat 1024 n = concreteWord n := by
  apply BitVec.eq_of_toNat_eq
  rfl
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

open Lean Meta Elab Term in
/-- Retain a weak-head value and its definitional equality without normalizing its fields. -/
elab "checked_whnf% " value:term : term => do
  let original ← instantiateMVars (← elabTerm value none)
  let normalized ← withTransparency .all (whnf original)
  logInfo m!"checkpoint head: {normalized.getAppFn.constName?}; argument heads: {normalized.getAppArgs.map fun argument => argument.getAppFn.constName?}"
  let equality ← mkEqRefl original
  let valueType ← inferType original
  let predicate ← withLocalDeclD `checkpoint valueType fun value => do
    mkLambdaFVars #[value] (← mkEq original value)
  mkAppOptM ``Subtype.mk #[some valueType, some predicate, some normalized, some equality]

private def checkpoint16 : { value : Outcome 1024 Node // execute 16 control before = value } :=
  checked_whnf% (execute 16 control before)
private def checkpoint32 : { value : Outcome 1024 Node // resume 16 checkpoint16.val = value } :=
  checked_whnf% (resume 16 checkpoint16.val)
private theorem prefix32 : execute 32 control before = checkpoint32.val := by
  change execute (16 + 16) control before = checkpoint32.val
  exact (execute_add 16 16 control before).trans
    ((congrArg (resume 16) checkpoint16.property).trans checkpoint32.property)
#print axioms prefix32
end MicroCFTA.GeneratedRowCaptureBackedgeFixture
