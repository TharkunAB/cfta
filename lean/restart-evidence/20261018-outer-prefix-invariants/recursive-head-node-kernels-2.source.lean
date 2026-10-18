import MicroCFTA.SourceCurrentRecursiveHeadNodeRows
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RecursiveHeadNodeKernels
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
private def openMu : Syntax Symbol Guard := .binder false (.node [.mk ("open",.top) selected [.var 0,nested]])
private def closedMu : Syntax Symbol Guard := .binder false (.node [.mk ("closed",.top) selected [nested,leaf]])
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [openMu,closedMu]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def first : Value Symbol Guard := ((children root)[0]?).getD .empty
private def second : Value Symbol Guard := ((children root)[1]?).getD .empty
private def firstUnfold := InternedFreshOrdinaryStoredSubstitution.unfold first heap
private def firstValue : Value Symbol Guard := match firstUnfold with | .done value _ => value | .pending .. => .empty
private def firstMade := run (makeNode (nodeEdges firstValue)) firstUnfold.state
private def secondUnfold := InternedFreshOrdinaryStoredSubstitution.unfold second firstMade.2
private def secondValue : Value Symbol Guard := match secondUnfold with | .done value _ => value | .pending .. => .empty
private def secondMade := run (makeNode (nodeEdges secondValue)) secondUnfold.state
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
private theorem first_head : Head first heap firstMade.1 firstMade.2 := by
  apply Head.read 0 (nodeEdges firstValue) firstUnfold.state
  · cbv
  · rfl
private theorem second_head : Head second firstMade.2 secondMade.1 secondMade.2 := by
  apply Head.read 0 (nodeEdges secondValue) secondUnfold.state
  · cbv
  · rfl

private theorem open_witness :
    built = .done root heap ∧
    ∃ entry bodyEntry originals level free depth ordinary,
      first = .mu entry (.node bodyEntry originals level free) depth ordinary ∧ free ≠ [] ∧
      Head first heap firstMade.1 firstMade.2 ∧ Keeps heap firstMade.2 ∧
      SourceCurrentRecursiveHeadNodeRows.Rows entry bodyEntry originals level free depth ordinary heap firstMade.1 firstMade.2 ∧
      (nodeEdges firstMade.1)[0]? = some firstRow ∧ firstRow.entry.key.constraint = selected ∧
      ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard),
        originals[sourceIndex]? = some original ∧
        RowCalls (selfEnvironment entry (.node bodyEntry originals level free) depth ordinary) firstMade.2 original firstRow ∧
        firstRow.children.length = 2 ∧
          (match firstRow.children[1]? with | some (.mu ..) => True | _ => False) := by
  have shape : ∃ entry bodyEntry originals level free depth ordinary,
      first = .mu entry (.node bodyEntry originals level free) depth ordinary ∧ free ≠ [] := by
    have tag : (match first with | .mu _ (.node _ _ _ free) _ _ => !free.isEmpty | _ => false) = true := by cbv
    cases found : first <;> simp only [found] at tag
    all_goals try cases tag
    rename_i entry body depth ordinary
    cases bodyShape : body <;> simp only [bodyShape] at tag
    all_goals try cases tag
    rename_i bodyEntry originals level free
    refine ⟨entry,bodyEntry,originals,level,free,depth,ordinary,rfl,?_⟩
    intro same
    rw [same] at tag
    cases tag
  obtain ⟨entry,bodyEntry,originals,level,free,depth,ordinary,shape,opened⟩ := shape
  have known := available.1
  have noFree := closed.1
  rw [shape] at known noFree
  obtain ⟨result,after,head,keeps,_,_,_,rows⟩ := SourceCurrentRecursiveHeadNodeRows.complete
    entry bodyEntry originals level free depth ordinary heap initial_ready known noFree
  have literal := first_head
  rw [shape] at literal
  obtain ⟨rfl,rfl⟩ := head.unique literal
  have positive : (nodeEdges firstMade.1)[0]? = some firstRow := by cbv
  have retained := rows
  obtain ⟨unfolded,middle,outputs,_,_,_,_,sources⟩ := rows
  obtain ⟨sourceIndex,original,found,_,calls,_⟩ := sources 0 firstRow positive
  refine ⟨built_done,entry,bodyEntry,originals,level,free,depth,ordinary,shape,opened,first_head,keeps,?_,positive,?_,
    sourceIndex,original,found,calls,?_,?_⟩
  · exact retained
  · cbv
  · cbv
  · cbv

private theorem closed_witness :
    Head first heap firstMade.1 firstMade.2 ∧ Keeps heap firstMade.2 ∧
    ∃ entry bodyEntry originals level free depth ordinary,
      second = .mu entry (.node bodyEntry originals level free) depth ordinary ∧ free = [] ∧
      Head second firstMade.2 secondMade.1 secondMade.2 ∧ Keeps firstMade.2 secondMade.2 ∧
      SourceCurrentRecursiveHeadNodeRows.Rows entry bodyEntry originals level free depth ordinary firstMade.2 secondMade.1 secondMade.2 ∧
      (nodeEdges secondMade.1)[0]? = some secondRow ∧ secondRow.entry.key.constraint = selected ∧
      ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard),
        originals[sourceIndex]? = some original ∧
        RowCalls (selfEnvironment entry (.node bodyEntry originals level free) depth ordinary) secondMade.2 original secondRow ∧
        secondRow.children.length = 2 ∧
          (match secondRow.children[0]? with | some (.mu ..) => True | _ => False) := by
  obtain ⟨value,after,firstHead,firstKeeps,_,_,_,_⟩ :=
    SourceCurrentRecursiveHeadRowOrigins.complete first heap initial_ready available.1 closed.1
  obtain ⟨rfl,rfl⟩ := firstHead.unique first_head
  have shape : ∃ entry bodyEntry originals level free depth ordinary,
      second = .mu entry (.node bodyEntry originals level free) depth ordinary ∧ free = [] := by
    have tag : (match second with | .mu _ (.node _ _ _ free) _ _ => free.isEmpty | _ => false) = true := by cbv
    cases found : second <;> simp only [found] at tag
    all_goals try cases tag
    rename_i entry body depth ordinary
    cases bodyShape : body <;> simp only [bodyShape] at tag
    all_goals try cases tag
    rename_i bodyEntry originals level free
    exact ⟨entry,bodyEntry,originals,level,free,depth,ordinary,rfl,List.isEmpty_iff.mp tag⟩
  obtain ⟨entry,bodyEntry,originals,level,free,depth,ordinary,shape,closedBody⟩ := shape
  have known := firstKeeps.available second available.2
  have noFree := closed.2
  have literal := second_head
  rw [shape] at known noFree literal
  obtain ⟨keeps,_,_,_,rows⟩ := SourceCurrentRecursiveHeadNodeRows.actual
    entry bodyEntry originals level free depth ordinary firstMade.2 firstKeeps.ready known noFree
    secondMade.1 secondMade.2 literal
  have positive : (nodeEdges secondMade.1)[0]? = some secondRow := by cbv
  have retained := rows
  obtain ⟨unfolded,middle,outputs,_,_,_,_,sources⟩ := rows
  obtain ⟨sourceIndex,original,found,_,calls,_⟩ := sources 0 secondRow positive
  refine ⟨first_head,firstKeeps,entry,bodyEntry,originals,level,free,depth,ordinary,shape,closedBody,
    second_head,keeps,retained,positive,?_,sourceIndex,original,found,calls,?_,?_⟩
  · cbv
  · cbv
  · cbv

end MicroCFTA.RecursiveHeadNodeKernels
