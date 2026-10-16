import MicroCFTA.SourceCurrentAllocatedNativeCodeProgress
open MicroCFTA
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeCodeProgress
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

#print axioms compileNode_operands
#print axioms children_certified
#print axioms sentinel_certified
#print axioms body_certified
#print axioms body_prefix
#print axioms node_certified
#print axioms initial_certified
#print axioms current_heap_inputs
#print axioms current_inputs

#check compileNode_operands
#check children_certified
#check sentinel_certified
#check body_certified
#check body_prefix
#check node_certified
#check initial_certified
#check current_heap_inputs
#check current_inputs

-- Empty has a complete memo codec. It is not a requestKey-none example.
example (width : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width domain
      (.empty : Value Symbol Guard) .empty = some key := ⟨_, rfl⟩

-- Unresolved intersection placeholders, unlike Empty, bypass memo lookup.
example (width : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    SourceRecursiveIntersectionMemo.requestKey width domain
      (.reference (.intersection 0 1) : Value Symbol Guard) .empty = none := rfl

-- No machine width makes an unresolved placeholder satisfy unconditional KeySafe.
example (width : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    ¬SourceRecursiveIntersectionMemo.KeySafe width domain
      (.reference (.intersection 0 1) : Value Symbol Guard) .empty := by
  simp [SourceRecursiveIntersectionMemo.KeySafe, Value.referenceOf, IntersectionFlatMemoKey.input]

-- The literal direct native call still completes and keeps both states unchanged.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (state : SourceEqualityNativeDemand.State width) :
    SourceEqualityNativeDemand.execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain
      (.reference (.intersection 0 1)) .empty)) state = .done .empty state := rfl

-- The older unconditional input plan cannot certify that arbitrary placeholder call.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (state : SourceEqualityNativeDemand.State width) :
    ¬SourceEqualityNativeDemandFieldExecution.InputsThrough holds 0
      (.code (requestNode IntersectionEmptyDomain.emptyDomain (.reference (.intersection 0 1)) .empty)) state := by
  simp [SourceEqualityNativeDemandFieldExecution.InputsThrough, SourceEqualityNativeDemandValidity.Inputs,
    requestNode, SourceRecursiveIntersectionMemo.KeySafe, Value.referenceOf, IntersectionFlatMemoKey.input]

-- Original syntax excludes exactly that unresolved-placeholder example.
example : ¬Original (.reference (.intersection 0 1) : Value Symbol Guard) := by
  intro original
  cases original

-- NodeBelow retains Original roots. The new adapter therefore derives KeySafe from conditional words.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (request : NodeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (ready : NodeReady state.native.machine request) (bounded : NodeBelow source holds bound request)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.node request Code.pure))) :
    SourceEqualityNativeDemandValidity.Inputs holds (.code (.node request Code.pure)) state :=
  current_inputs source holds bound (.node request Code.pure) state
    ⟨ready, fun _ _ _ _ _ => trivial⟩ ⟨bounded, fun _ _ _ _ _ => trivial⟩ words

-- A sentinel derives its actual current constructor operands without child calls or semantic receipts.
example [DecidableEq (EdgeKey Symbol Guard)] (left : EdgeValue Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceRecursiveIntersectionKernel.Valid state.native.machine) :
    SourceEqualityNativeDemandHeap.Inputs (.code (SourceEqualityNativeCheckedCode.sentinel left)) state :=
  current_heap_inputs _ state (sentinel_certified left state.native.machine valid).2
