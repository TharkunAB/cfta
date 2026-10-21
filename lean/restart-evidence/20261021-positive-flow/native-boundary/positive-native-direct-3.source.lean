import MicroCFTA.SourceCurrentRequiredPositivePosition
import MicroCFTA.SourceCurrentNativePositiveRowOrigins
import MicroCFTA.SourceCurrentNativeKeyAdmission
import MicroCFTA.SourceCurrentNativeRowKeyable
import MicroCFTA.SourceCurrentSharedLeafNativeLineage
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceEqualityNormalizationReceipt
/-!
# Opaque Mu inputs do not retain positive ordinary positions

Both raw source binders have closed bodies. The source builder retains them.
The actual native query exposes the bodies and returns a positive ordinary row.
The initial native result tables are empty.
-/
set_option linter.all true
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.PositiveNativeSupportKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) top []]
private def first : Syntax Symbol Guard := .binder false (.node [.mk ("pair",.top) top [leaf,leaf]])
private def second : Syntax Symbol Guard := .binder false (.node [.mk ("pair",.top) own [leaf,leaf]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [first,second]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def firstAllocation := SourceEqualityConstraintAllocation.construct top.equalities Cache.emptyState
private def firstValue := match firstAllocation.1 with | .ok value => value | .error _ => .contradiction
private def secondAllocation := SourceEqualityConstraintAllocation.construct own.equalities firstAllocation.2
private def secondValue := match secondAllocation.1 with | .ok value => value | .error _ => .contradiction
private def before : Checked 130 :=
  ⟨initial 130 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial secondAllocation.2⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain left right)
private noncomputable def cold := execute 64 control before
private noncomputable def output : Node := match cold with | .done value _ => value | _ => .empty
private noncomputable def after := cold.state
private noncomputable def row : Row := (nodeEdges output)[0]?.getD (run (makeEdge ("fallback",.top) top []) heap).1
private noncomputable def child : Node := row.children[0]?.getD .empty
private theorem built_done : built = .done root heap := by cbv
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready before := by
  have cached : SourceEqualityGuardReadback.Cached own.equalities := by
    intro classes same
    cases same
    exact SourceEqualityGuardReadback.normalized
      (show EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] by cbv)
  have firstHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState firstAllocation.2 [top] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
      (show firstAllocation = (.ok firstValue,firstAllocation.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState secondAllocation.2 [top,own] :=
    SourceEqualityOriginalAllocationHistory.History.construct firstHistory cached
      (show secondAllocation = (.ok secondValue,secondAllocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [top,own] := by
    intro guard member
    simp only [expression,first,second,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,or_self] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 130 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem initial_good : Good before := initial_ready.good
private theorem available : Available heap left ∧ Available heap right := by
  have source := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
  constructor
  · exact source.children left (by cbv; exact .head _)
  · exact source.children right (by cbv; exact .tail _ (.head _))
private theorem cold_done : cold = .done output after := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases actual : cold <;> simp_all only [output,after,Outcome.state,Bool.false_eq_true]
private theorem shape_left : ∃ entry body depth ordinary,
    left = .mu entry body depth ordinary ∧ body.free = [] := by
  cases observed : left with
  | mu entry body depth ordinary =>
      exact ⟨entry,body,depth,ordinary,rfl,by cbv at observed; cases observed; rfl⟩
  | empty | reference | node | union => cbv at observed; cases observed
private theorem shape_right : ∃ entry body depth ordinary,
    right = .mu entry body depth ordinary ∧ body.free = [] := by
  cases observed : right with
  | mu entry body depth ordinary =>
      exact ⟨entry,body,depth,ordinary,rfl,by cbv at observed; cases observed; rfl⟩
  | empty | reference | node | union => cbv at observed; cases observed
private theorem no_positive_mu (entry body depth ordinary) :
    ∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt
      (Value.mu entry body depth ordinary : Node) path := by
  intro path positive
  cases positive
private theorem selected : (nodeEdges output)[0]? = some row := by cbv
private theorem positive : SourceMemoGate.plain row.entry.key.constraint = false := by cbv

private theorem checked_witness :
    ∃ (program : Syntax Symbol Guard) (input : Node) (source : State Symbol Guard)
      (operations : SourceEqualityConstraintMemoAllocation.State)
      (initial final : Checked 130) (left right result : Node) (row : Row),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input source ∧
      initial = ⟨SourceRecursiveIntersectionThunks.initial 130 ⟨source,Cache.emptyState⟩,operations⟩ ∧
      Good initial ∧ Available source left ∧ Available source right ∧ left ≠ right ∧
      (∃ entry body depth ordinary, left = .mu entry body depth ordinary ∧ body.free = []) ∧
      (∃ entry body depth ordinary, right = .mu entry body depth ordinary ∧ body.free = []) ∧
      (∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt left path) ∧
      (∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt right path) ∧
      execute 64 (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) initial = .done result final ∧
      (∃ count, Trace count (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        initial (.code (.pure result)) final) ∧
      (nodeEdges result)[0]? = some row ∧ SourceMemoGate.plain row.entry.key.constraint = false ∧
      SourceCurrentRequiredPositivePosition.PositiveAt result [] := by
  obtain ⟨count,_,traced,_,_,_⟩ := SourceCurrentNativeKeyAdmission.node_done 128 64 before initial_good
    initial_ready.semantic left right available.1 available.2 (by cbv) (by cbv)
    (by cbv) (by cbv) (by cbv) cold_done
  have positive_output : SourceCurrentRequiredPositivePosition.PositiveAt output [] := by
    cases shape : output with
    | node entry rows depth free =>
        exact .root 0 row (by simpa only [shape,nodeEdges] using selected) positive
    | empty | reference | mu | union =>
        have absent := selected
        simp only [shape,nodeEdges] at absent
        cases absent
  have no_left : ∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt left path := by
    obtain ⟨entry,body,depth,ordinary,same,_⟩ := shape_left
    rw [same]
    exact no_positive_mu entry body depth ordinary
  have no_right : ∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt right path := by
    obtain ⟨entry,body,depth,ordinary,same,_⟩ := shape_right
    rw [same]
    exact no_positive_mu entry body depth ordinary
  exact ⟨expression,root,heap,SourceEqualityConstraintMemoAllocation.initial secondAllocation.2,
    before,after,left,right,output,row,built_done,rfl,initial_good,available.1,available.2,
    by
      intro same
      have different : (left.referenceOf == right.referenceOf) = false := by cbv
      simp only [same,beq_self_eq_true] at different
      cases different,shape_left,shape_right,no_left,no_right,cold_done,⟨count,traced⟩,selected,positive,positive_output⟩

/-- Actual empty-table native execution exposes a positive row from two opaque raw Mu inputs. -/
theorem actual_opaque_mu_counterexample :
    ∃ (program : Syntax Symbol Guard) (input : Node) (source : State Symbol Guard)
      (operations : SourceEqualityConstraintMemoAllocation.State)
      (initial final : Checked 130) (left right result : Node) (row : Row),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input source ∧
      initial = ⟨SourceRecursiveIntersectionThunks.initial 130 ⟨source,Cache.emptyState⟩,operations⟩ ∧
      Good initial ∧ Available source left ∧ Available source right ∧ left ≠ right ∧
      (∃ entry body depth ordinary, left = .mu entry body depth ordinary ∧ body.free = []) ∧
      (∃ entry body depth ordinary, right = .mu entry body depth ordinary ∧ body.free = []) ∧
      (∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt left path) ∧
      (∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt right path) ∧
      execute 64 (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) initial = .done result final ∧
      (∃ count, Trace count (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        initial (.code (.pure result)) final) ∧
      (nodeEdges result)[0]? = some row ∧ SourceMemoGate.plain row.entry.key.constraint = false ∧
      SourceCurrentRequiredPositivePosition.PositiveAt result [] := checked_witness

end MicroCFTA.PositiveNativeSupportKernels
