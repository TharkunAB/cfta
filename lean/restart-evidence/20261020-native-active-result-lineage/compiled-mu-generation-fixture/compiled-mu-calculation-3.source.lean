import MicroCFTA.SourceCurrentNativeOriginGeneration
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceEqualityNormalizationReceipt

noncomputable section
namespace MicroCFTA.CompiledMuGenerationFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
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
set_option maxRecDepth 100000
set_option cbv.maxSteps 100000000
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def concreteWord (n : Nat) : BitVec 128 :=
  if h : n < 1024 then BitVec.ofNatLT n (Nat.lt_of_lt_of_le h (by decide : 1024 ≤ 2^128))
  else BitVec.ofNat 128 n
private theorem word_small (n : Nat) : BitVec.ofNat 128 n = concreteWord n := by
  unfold concreteWord
  split
  · apply BitVec.eq_of_toNat_eq
    change n % 2^128 = n
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by assumption) (by decide : 1024 ≤ 2^128))
  · rfl
attribute [local cbv_eval] word_small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def recursive (label : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("rec",.top) top [.var 0],.mk (label,.top) top []])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("pair",.top) top [recursive "left",recursive "right"]]
private def built := InternedFreshOrdinaryConstruction.build expression [] (empty : Heap)
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def allocatedOps := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def before : Checked 128 := ⟨initial 128 machine,allocatedOps⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain request.left request.right)
private def result := execute 64 control before
private def value : Node := match result with | .done output _ => output | _ => .empty
private def after : Checked 128 := result.state
private def entry : Interned InternedBinderProtocol.NodeKey := match value with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def stored : Node := match value with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def depth : Node := match value with | .mu _ _ probe _ => probe | _ => .empty
private def ordinary : Node := match value with | .mu _ _ _ probe => probe | _ => .empty
private theorem built_done : built = .done root heap := by cbv
private theorem returned : result = .done value after := by cbv
private theorem new_mu : value = .mu entry stored depth ordinary ∧
    heap.nodeRecords entry.key = none ∧
    after.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    InternedBinderProtocol.Reference.interned entry.identity ∈ stored.free := by
  constructor
  · cbv
  constructor
  · cbv
  constructor
  · cbv
  · cbv
    exact List.mem_cons_self
end MicroCFTA.CompiledMuGenerationFixture
