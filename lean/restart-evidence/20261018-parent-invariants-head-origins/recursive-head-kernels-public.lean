import MicroCFTA.SourceCurrentRecursiveHeadRowOrigins
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RecursiveHeadKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredHead (Head)
open SourceEqualityRequiredCache (Ready Keeps)
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
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) plain [],.mk ("pair",.top) selected [.var 0,.var 0]])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("root",.top) plain [recursive,.union [recursive,leaf]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def value : Value Symbol Guard := ((children root)[0]?).getD .empty
private def choice : Value Symbol Guard := ((children root)[1]?).getD .empty
private def unfolding := InternedFreshOrdinaryStoredSubstitution.unfold value heap
private def unfolded : Value Symbol Guard := match unfolding with | .done value _ => value | .pending .. => .empty
private def middle := unfolding.state
private def made := run (makeNode (nodeEdges unfolded)) middle
private def pairRow : EdgeValue Symbol Guard := ((nodeEdges made.1)[1]?).getD
  (run (makeEdge ("unused",.top) plain []) empty).1

private theorem built_done : built = .done root heap := by
  obtain ⟨value,state,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,root,heap,done,InternedNestedConstruction.Outcome.state]
private theorem initial_ready : Ready heap := SourceEqualityRequiredCache.constructed expression root heap built_done
private theorem available : Available heap value ∧ Available heap choice := by
  have rootAvailable := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
  constructor
  · exact rootAvailable.children value (by cbv; exact .head _)
  · exact rootAvailable.children choice (by cbv; exact .tail _ (.head _))
private theorem closed : value.free = [] ∧ choice.free = [] := by constructor <;> cbv
private theorem actual_head : Head value heap made.1 made.2 := by
  apply Head.read 0 (nodeEdges unfolded) middle
  · cbv
  · rfl
private theorem selected_row : (nodeEdges made.1)[1]? = some pairRow := by cbv

/-- Initial source data constructs an actual retained Mu Head with a positive full-guard row. -/
private theorem checked_mu_head :
    built = .done root heap ∧ Available heap value ∧ value.free = [] ∧
    (∃ entry body depth ordinary, value = .mu entry body depth ordinary ∧
      (∃ source rows level free, body = .node source rows level free ∧ free ≠ [])) ∧
    Head value heap made.1 made.2 ∧ Keeps heap made.2 ∧
    SourceCurrentRecursiveHeadRowOrigins.HeadRows value heap made.1 made.2 ∧
    (nodeEdges made.1)[1]? = some pairRow ∧ pairRow.entry.key.constraint = selected ∧
    pairRow.children.length = 2 := by
  obtain ⟨result,after,head,kept,_,_,_,origins⟩ :=
    SourceCurrentRecursiveHeadRowOrigins.complete value heap initial_ready available.1 closed.1
  obtain ⟨rfl,rfl⟩ := head.unique actual_head
  refine ⟨built_done,available.1,closed.1,?_,actual_head,kept,origins,selected_row,?_,?_⟩
  · have tag : (match value with
        | .mu _ (.node _ _ _ free) _ _ => !free.isEmpty
        | _ => false) = true := by cbv
    cases shape : value <;> simp only [shape] at tag
    all_goals try cases tag
    rename_i entry body depth ordinary
    cases bodyShape : body <;> simp only [bodyShape] at tag
    all_goals try cases tag
    rename_i source rows level free
    refine ⟨entry,.node source rows level free,depth,ordinary,rfl,source,rows,level,free,rfl,?_⟩
    intro empty
    rw [empty] at tag
    cases tag
  · cbv
  · cbv

private theorem union_head : Head choice made.2 made.1 made.2 := by
  apply Head.read 8 (nodeEdges made.1) made.2
  · cbv
  · cbv

/-- A second actual Head consumes the original union at the first returned heap and retains its Mu member origin. -/
private theorem checked_union_after_mu :
    Head value heap made.1 made.2 ∧ Keeps heap made.2 ∧
    Head choice made.2 made.1 made.2 ∧
    SourceCurrentRecursiveHeadRowOrigins.HeadRows choice made.2 made.1 made.2 ∧
    (nodeEdges made.1)[1]? = some pairRow ∧ pairRow.entry.key.constraint = selected ∧
    ∃ entry members level free, choice = .union entry members level free ∧
      ∃ (index : Nat) (member : Value Symbol Guard), members[index]? = some member ∧ MergedFreshOrdinaryGraph.Origin made.2 [member] pairRow := by
  obtain ⟨result,after,head,kept,_,_,_,_⟩ :=
    SourceCurrentRecursiveHeadRowOrigins.complete value heap initial_ready available.1 closed.1
  obtain ⟨rfl,rfl⟩ := head.unique actual_head
  obtain ⟨result,after,head,_,_,_,_,origins⟩ := SourceCurrentRecursiveHeadRowOrigins.complete choice made.2
    kept.ready (kept.available choice available.2) closed.2
  obtain ⟨rfl,rfl⟩ := head.unique union_head
  refine ⟨actual_head,kept,union_head,origins,selected_row,?_,?_⟩
  · cbv
  · have shape : ∃ entry members level free, choice = .union entry members level free := by
      have tag : (match choice with | .union .. => true | _ => false) = true := by cbv
      cases shape : choice <;> simp only [shape] at tag
      all_goals try cases tag
      exact ⟨_,_,_,_,rfl⟩
    obtain ⟨entry,members,level,free,shape⟩ := shape
    refine ⟨entry,members,level,free,shape,?_⟩
    rw [shape] at origins
    exact origins 1 pairRow selected_row

/-- The exact checked Mu witness retains the actual source and full returned state. -/
theorem mu_head :
    built = .done root heap ∧ Available heap value ∧ value.free = [] ∧
    (∃ entry body depth ordinary, value = .mu entry body depth ordinary ∧
      (∃ source rows level free, body = .node source rows level free ∧ free ≠ [])) ∧
    Head value heap made.1 made.2 ∧ Keeps heap made.2 ∧
    SourceCurrentRecursiveHeadRowOrigins.HeadRows value heap made.1 made.2 ∧
    (nodeEdges made.1)[1]? = some pairRow ∧ pairRow.entry.key.constraint = selected ∧
    pairRow.children.length = 2 := checked_mu_head

/-- The exact sequential union witness retains its selected original member. -/
theorem union_after_mu :
    Head value heap made.1 made.2 ∧ Keeps heap made.2 ∧
    Head choice made.2 made.1 made.2 ∧
    SourceCurrentRecursiveHeadRowOrigins.HeadRows choice made.2 made.1 made.2 ∧
    (nodeEdges made.1)[1]? = some pairRow ∧ pairRow.entry.key.constraint = selected ∧
    ∃ entry members level free, choice = .union entry members level free ∧
      ∃ (index : Nat) (member : Value Symbol Guard), members[index]? = some member ∧ MergedFreshOrdinaryGraph.Origin made.2 [member] pairRow := checked_union_after_mu

end MicroCFTA.RecursiveHeadKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.RecursiveHeadKernels.mu_head
#print MicroCFTA.RecursiveHeadKernels.mu_head
#print axioms MicroCFTA.RecursiveHeadKernels.mu_head

#check @MicroCFTA.RecursiveHeadKernels.union_after_mu
#print MicroCFTA.RecursiveHeadKernels.union_after_mu
#print axioms MicroCFTA.RecursiveHeadKernels.union_after_mu

