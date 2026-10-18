import MicroCFTA.SourceCurrentRecursiveHeadChainRows
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RecursiveHeadChainKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredHead (Head)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
open SourceCurrentStoredNodeExpansion (RowCalls)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := SourceEqualityConstraintConstructors.top
private def selected : Guard := ⟨some [[[0],[1]]],.same [0] [1]⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def nested : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) plain [],.mk ("pair",.top) plain [.var 0,.var 0]])
private def nestedRoot : Syntax Symbol Guard := .binder false (.binder false
  (.node [.mk ("nested",.top) selected [.var 1,.var 0,nested]]))
private def unionRoot : Syntax Symbol Guard := .union [nestedRoot,leaf]
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [nestedRoot,unionRoot]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def first : Value Symbol Guard := ((children root)[0]?).getD .empty
private def second : Value Symbol Guard := ((children root)[1]?).getD .empty
private def firstRead := MergedFreshOrdinaryExposure.nodeEdges 32 first heap
private def firstEdges : List (EdgeValue Symbol Guard) := match firstRead with | .done rows _ => rows | _ => []
private def firstMade := run (makeNode firstEdges) firstRead.state
private def secondRead := MergedFreshOrdinaryExposure.nodeEdges 32 second firstMade.2
private def secondEdges : List (EdgeValue Symbol Guard) := match secondRead with | .done rows _ => rows | _ => []
private def secondMade := run (makeNode secondEdges) secondRead.state
private def firstRow : EdgeValue Symbol Guard := ((nodeEdges firstMade.1)[0]?).getD
  (run (makeEdge ("unused",.top) plain []) empty).1
private def secondRow : EdgeValue Symbol Guard := ((nodeEdges secondMade.1)[0]?).getD
  (run (makeEdge ("unused",.top) plain []) empty).1

private theorem built_done : built = .done root heap := by
  obtain ⟨value,state,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,root,heap,done,InternedNestedConstruction.Outcome.state]
private theorem initial_ready : Ready heap := SourceEqualityRequiredCache.constructed expression root heap built_done
private theorem available : Available heap first ∧ Available heap second := by
  have rootAvailable := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
  constructor
  · exact rootAvailable.children first (by cbv; exact .head _)
  · exact rootAvailable.children second (by cbv; exact .tail _ (.head _))
private theorem closed : first.free = [] ∧ second.free = [] := by constructor <;> cbv
private theorem first_read : firstRead = .done firstEdges firstRead.state := by
  have tag : (match firstRead with | .done .. => true | _ => false) = true := by cbv
  cases found : firstRead <;> simp_all only [firstEdges,MergedSourceExposure.Result.state,Bool.false_eq_true]
private theorem second_read : secondRead = .done secondEdges secondRead.state := by
  have tag : (match secondRead with | .done .. => true | _ => false) = true := by cbv
  cases found : secondRead <;> simp_all only [secondEdges,MergedSourceExposure.Result.state,Bool.false_eq_true]
private theorem first_head : Head first heap firstMade.1 firstMade.2 := .read 32 firstEdges firstRead.state first_read rfl
private theorem second_head : Head second firstMade.2 secondMade.1 secondMade.2 :=
  .read 32 secondEdges secondRead.state second_read rfl

private theorem nested_witness :
    built = .done root heap ∧
    (match first with | .mu _ (.mu ..) _ _ => True | _ => False) ∧
    Head first heap firstMade.1 firstMade.2 ∧ Keeps heap firstMade.2 ∧
    SourceCurrentRecursiveHeadChainRows.Rows first heap firstMade.1 firstMade.2 ∧
    (nodeEdges firstMade.1)[0]? = some firstRow ∧ firstRow.entry.key.constraint = selected ∧
    firstRow.children.length = 3 ∧
    ∃ (terminal : State Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey)
      (originals : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) (sourceIndex : Nat),
      ∃ branch : SourceCurrentRecursiveHeadChainRows.Chain heap first terminal (.node entry originals depth free),
        Keeps terminal firstMade.2 ∧ SourceCurrentRecursiveHeadChainRows.Warm firstMade.2 branch ∧
        originals[sourceIndex]? = some firstRow ∧ RowCalls (fun _ => none) firstMade.2 firstRow firstRow := by
  obtain ⟨result,after,head,keeps,_,_,_,rows⟩ := SourceCurrentRecursiveHeadChainRows.complete
    first heap initial_ready available.1 closed.1
  obtain ⟨rfl,rfl⟩ := head.unique first_head
  have positive : (nodeEdges firstMade.1)[0]? = some firstRow := by cbv
  refine ⟨built_done,?_,first_head,keeps,rows,positive,?_,?_,?_⟩
  · cbv
  · cbv
  · cbv
  · exact rows 0 firstRow positive

private theorem union_witness :
    Head first heap firstMade.1 firstMade.2 ∧ Keeps heap firstMade.2 ∧
    (match second with | .union .. => True | _ => False) ∧
    Head second firstMade.2 secondMade.1 secondMade.2 ∧ Keeps firstMade.2 secondMade.2 ∧
    SourceCurrentRecursiveHeadChainRows.Rows second firstMade.2 secondMade.1 secondMade.2 ∧
    (nodeEdges secondMade.1)[0]? = some secondRow ∧
    0 < (nodeEdges secondMade.1).length ∧
    ∃ (terminal : State Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey)
      (originals : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) (sourceIndex : Nat),
      ∃ branch : SourceCurrentRecursiveHeadChainRows.Chain firstMade.2 second terminal (.node entry originals depth free),
        Keeps terminal secondMade.2 ∧ SourceCurrentRecursiveHeadChainRows.Warm secondMade.2 branch ∧
        originals[sourceIndex]? = some secondRow ∧ RowCalls (fun _ => none) secondMade.2 secondRow secondRow := by
  have first := SourceCurrentRecursiveHeadChainRows.actual first heap initial_ready available.1 closed.1
    firstMade.1 firstMade.2 first_head
  have known := first.1.available second available.2
  obtain ⟨keeps,_,_,_,rows⟩ := SourceCurrentRecursiveHeadChainRows.actual
    second firstMade.2 first.1.ready known closed.2 secondMade.1 secondMade.2 second_head
  have positive : (nodeEdges secondMade.1)[0]? = some secondRow := by cbv
  refine ⟨first_head,first.1,?_,second_head,keeps,rows,positive,?_,?_⟩
  · cbv
  · cbv
  · exact rows 0 secondRow positive

/-- A source-built Mu with a Mu body retains chronological terminal rows. -/
theorem nested_mu_root :
    built = .done root heap ∧
    (match first with | .mu _ (.mu ..) _ _ => True | _ => False) ∧
    Head first heap firstMade.1 firstMade.2 ∧ Keeps heap firstMade.2 ∧
    SourceCurrentRecursiveHeadChainRows.Rows first heap firstMade.1 firstMade.2 ∧
    (nodeEdges firstMade.1)[0]? = some firstRow ∧ firstRow.entry.key.constraint = selected ∧
    firstRow.children.length = 3 ∧
    ∃ (terminal : State Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey)
      (originals : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) (sourceIndex : Nat),
      ∃ branch : SourceCurrentRecursiveHeadChainRows.Chain heap first terminal (.node entry originals depth free),
        Keeps terminal firstMade.2 ∧ SourceCurrentRecursiveHeadChainRows.Warm firstMade.2 branch ∧
        originals[sourceIndex]? = some firstRow ∧ RowCalls (fun _ => none) firstMade.2 firstRow firstRow := nested_witness

/-- A union Head retains its terminal rows at the first actual returned heap. -/
theorem union_after_nested :
    Head first heap firstMade.1 firstMade.2 ∧ Keeps heap firstMade.2 ∧
    (match second with | .union .. => True | _ => False) ∧
    Head second firstMade.2 secondMade.1 secondMade.2 ∧ Keeps firstMade.2 secondMade.2 ∧
    SourceCurrentRecursiveHeadChainRows.Rows second firstMade.2 secondMade.1 secondMade.2 ∧
    (nodeEdges secondMade.1)[0]? = some secondRow ∧
    0 < (nodeEdges secondMade.1).length ∧
    ∃ (terminal : State Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey)
      (originals : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) (sourceIndex : Nat),
      ∃ branch : SourceCurrentRecursiveHeadChainRows.Chain firstMade.2 second terminal (.node entry originals depth free),
        Keeps terminal secondMade.2 ∧ SourceCurrentRecursiveHeadChainRows.Warm secondMade.2 branch ∧
        originals[sourceIndex]? = some secondRow ∧ RowCalls (fun _ => none) secondMade.2 secondRow secondRow := union_witness

end MicroCFTA.RecursiveHeadChainKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.RecursiveHeadChainKernels.nested_mu_root
#print MicroCFTA.RecursiveHeadChainKernels.nested_mu_root
#print axioms MicroCFTA.RecursiveHeadChainKernels.nested_mu_root

#check @MicroCFTA.RecursiveHeadChainKernels.union_after_nested
#print MicroCFTA.RecursiveHeadChainKernels.union_after_nested
#print axioms MicroCFTA.RecursiveHeadChainKernels.union_after_nested
