import MicroCFTA.SourceCurrentNativeReferenceOrigins

/-!
# Complete request keys at actual ordinary native rows

An unresolved request can return only literal Empty. The proof follows
its actual finite trace, including any operand swap. A selected ordinary
row therefore derives both complete input codecs and a native memo key.
-/
namespace MicroCFTA.SourceCurrentNativeRowKeyable
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionControl (decision identity reset closedSelf)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

private theorem closed_keyable (value : Value Symbol Guard) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free,Value.referenceOf,IntersectionFlatMemoKey.input]

private theorem identity_keyable (value : Value Symbol Guard) (name : Nat) (named : identity value = some name) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value with
  | reference reference => cases reference <;> simp_all [identity,Value.referenceOf,IntersectionFlatMemoKey.input]
  | empty | node | mu | union => simp_all [identity,Value.referenceOf,IntersectionFlatMemoKey.input]

private theorem no_codecs (request : NodeRequest Symbol Guard)
    (missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none)
    (first : ∃ input, IntersectionFlatMemoKey.input request.left.referenceOf = some input)
    (second : ∃ input, IntersectionFlatMemoKey.input request.right.referenceOf = some input) : False := by
  obtain ⟨left,leftInput⟩ := first
  obtain ⟨right,rightInput⟩ := second
  have key := IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ left right leftInput rightInput
  change IntersectionFlatMemoKeyDomain.sourceKey width request.domain request.left.referenceOf request.right.referenceOf = none at missing
  rw [key] at missing
  cases missing

private theorem unkeyed_control (request : NodeRequest Symbol Guard)
    (missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none) :
    decision request.domain.key request.left request.right = .empty ∨
      decision request.domain.key request.left request.right = .swap ∨
      decision request.domain.key request.left request.right = .unsupported := by
  have noReset : reset request.domain.key request.left request.right = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    have tests : (request.left.free = [] ∧ request.right.free = []) ∧ (!request.domain.key.free.isEmpty) = true := by
      simpa only [reset,Bool.and_eq_true,List.isEmpty_iff] using selected
    exact no_codecs request missing (closed_keyable _ tests.1.1) (closed_keyable _ tests.1.2)
  have noSelf : closedSelf request.left request.right = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    have tests : request.left.referenceOf = request.right.referenceOf ∧ request.left.free = [] := by
      simpa only [closedSelf,Bool.and_eq_true,beq_iff_eq,List.isEmpty_iff] using selected
    obtain ⟨input,codec⟩ := closed_keyable _ tests.2
    exact no_codecs request missing ⟨input,codec⟩ ⟨input,by rw [← tests.1]; exact codec⟩
  cases first : identity request.left <;> cases second : identity request.right
  all_goals try exact (no_codecs request missing (identity_keyable _ _ first) (identity_keyable _ _ second)).elim
  all_goals
    simp only [decision,noReset,noSelf,first,second,Bool.false_eq_true,ite_false]
    split <;> simp_all

private theorem unkeyed_swap (request : NodeRequest Symbol Guard)
    (missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none) :
    SourceRecursiveIntersectionMemo.requestKey width request.domain request.right request.left = none := by
  cases left : IntersectionFlatMemoKey.input request.left.referenceOf <;>
    cases right : IntersectionFlatMemoKey.input request.right.referenceOf <;>
    simp_all [SourceRecursiveIntersectionMemo.requestKey,IntersectionFlatMemoKeyDomain.sourceKey,IntersectionFlatMemoKey.key]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem failed_body {before after : Checked width} (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (.fail failure)) before (.code (.pure result)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ _ one _ => cases one

/-- An actual successful unresolved native request returns literal Empty. -/
theorem unkeyed_empty {before after : Checked width} (request : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard)
    (missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure result)) after) :
    result = .empty := by
  induction fuel using Nat.strongRecOn generalizing before after request result with
  | ind fuel ih =>
    cases actual with
    | cons _ _ next current _ _ count _ one tail =>
      have selected := lookupNode_bypass width request before.native missing
      obtain ⟨rfl,rfl⟩ := Outcome.yielded.inj (by
        simpa only [step,SourceRecursiveIntersectionNative.step,requestNode,selected,lift] using one)
      have bodyTrace : Trace count (.code (compileNode request)) before (.code (.pure result)) after := by
        simpa only [code_bind_pure] using tail
      rcases unkeyed_control request missing with empty | swap | unsupported
      · have compiled : compileNode request = .pure .empty := by simp only [compileNode,empty]
        rw [compiled] at bodyTrace
        exact (pure_trace count .empty result before after bodyTrace.steps).2.1.symm
      · have compiled : compileNode request = requestNode request.domain request.right request.left := by
          simp only [compileNode,swap]
        rw [compiled] at bodyTrace
        exact ih count (by omega) ⟨request.domain,request.right,request.left⟩ result
          (unkeyed_swap request missing) bodyTrace
      · exact (failed_body count _ result (by simpa only [compileNode,unsupported,SourceRecursiveIntersectionCode.unsupported] using bodyTrace)).elim

/-- A physical ordinary result row derives both input codecs and the actual native request key. -/
theorem selected {before after : Checked width} (request : NodeRequest Symbol Guard)
    (fuel : Nat) (result : Value Symbol Guard)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure result)) after)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ first second key,
      IntersectionFlatMemoKey.input request.left.referenceOf = some first ∧
      IntersectionFlatMemoKey.input request.right.referenceOf = some second ∧
      SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  cases left : IntersectionFlatMemoKey.input request.left.referenceOf with
  | none =>
    have missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none := by
      simp [SourceRecursiveIntersectionMemo.requestKey,IntersectionFlatMemoKeyDomain.sourceKey,IntersectionFlatMemoKey.key,left]
    have empty := unkeyed_empty request fuel result missing actual
    simp only [empty,nodeEdges,List.getElem?_nil] at selected
    cases selected
  | some first =>
    cases right : IntersectionFlatMemoKey.input request.right.referenceOf with
    | none =>
      have missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none := by
        simp [SourceRecursiveIntersectionMemo.requestKey,IntersectionFlatMemoKeyDomain.sourceKey,IntersectionFlatMemoKey.key,left,right]
      have empty := unkeyed_empty request fuel result missing actual
      simp only [empty,nodeEdges,List.getElem?_nil] at selected
      cases selected
    | some second =>
      exact ⟨first,second,_,rfl,rfl,
        IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ first second left right⟩

end MicroCFTA.SourceCurrentNativeRowKeyable
