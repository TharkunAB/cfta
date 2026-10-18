import MicroCFTA.SourceCurrentRecursiveHeadUnionRows
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RecursiveHeadUnionKernels
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
private def expression : Syntax Symbol Guard := .binder false (.union [
  .node [.mk ("chosen",.top) selected [.var 0,nested]],
  .binder false (.node [.mk ("inner",.top) plain [.var 0,.var 1]])])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def exposed := MergedFreshOrdinaryExposure.nodeEdges 32 root heap
private def rawRows : List (EdgeValue Symbol Guard) := match exposed with | .done rows _ => rows | _ => []
private def made := run (makeNode rawRows) exposed.state
private def source : Value Symbol Guard := match root with
  | .mu _ (.union _ members _ _) _ _ => (members[0]?).getD .empty
  | _ => .empty
private def environment : InternedStoredSubstitution.Environment Symbol Guard := match root with
  | .mu entry body depth ordinary => selfEnvironment entry body depth ordinary
  | _ => fun _ => none
private def sourceRun := InternedFreshOrdinaryStoredSubstitution.execute source environment made.2
private def sourceValue : Value Symbol Guard := match sourceRun with | .done value _ => value | _ => .empty
private def chosenRow : EdgeValue Symbol Guard := ((nodeEdges sourceValue)[0]?).getD
  (run (makeEdge ("unused",.top) plain []) empty).1

private theorem built_done : built = .done root heap := by
  obtain ⟨value,state,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,root,heap,done,InternedNestedConstruction.Outcome.state]
private theorem initial_ready : Ready heap := SourceEqualityRequiredCache.constructed expression root heap built_done
private theorem available : Available heap root := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem closed : root.free = [] := by cbv
private theorem read_done : exposed = .done rawRows exposed.state := by
  have tag : (match exposed with | .done .. => true | _ => false) = true := by cbv
  cases found : exposed <;> simp_all only [rawRows,MergedSourceExposure.Result.state,Bool.false_eq_true]
private theorem head : Head root heap made.1 made.2 := .read 32 rawRows exposed.state read_done rfl
private theorem paired_forward {A B : Type} {relation : A → B → Prop} {originals : List A} {outputs : List B}
    (paired : All₂ relation originals outputs) (original : A) (index : Nat) (selected : originals[index]? = some original) :
    ∃ output, outputs[index]? = some output ∧ relation original output := by
  induction paired generalizing index with
  | nil => simp at selected
  | cons first rest ih =>
    cases index with
    | zero =>
      have same := Option.some.inj selected
      subst original
      exact ⟨_,rfl,first⟩
    | succ index => exact ih index (by simpa using selected)

private theorem witness :
    built = .done root heap ∧ Head root heap made.1 made.2 ∧ Keeps heap made.2 ∧
    source.free ≠ [] ∧ (match source with | .node .. => True | _ => False) ∧
    (nodeEdges made.1)[0]? = some chosenRow ∧ chosenRow.entry.key.constraint = selected ∧
    chosenRow.children.length = 2 ∧
    SourceCurrentRecursiveHeadUnionRows.MemberRows environment made.2 source chosenRow ∧
    ∃ (entry bodyEntry : Interned InternedBinderProtocol.NodeKey) (originals : List (Value Symbol Guard))
      (level : Nat) (free : List InternedBinderProtocol.Reference) (depth ordinary : Value Symbol Guard),
      root = .mu entry (.union bodyEntry originals level free) depth ordinary ∧
      SourceCurrentRecursiveHeadUnionRows.Rows entry bodyEntry originals level free depth ordinary heap made.1 made.2 := by
  have shape : ∃ (entry bodyEntry : Interned InternedBinderProtocol.NodeKey) (originals : List (Value Symbol Guard))
      (level : Nat) (free : List InternedBinderProtocol.Reference) (depth ordinary : Value Symbol Guard),
      root = .mu entry (.union bodyEntry originals level free) depth ordinary := by
    have tag : (match root with | .mu _ (.union ..) _ _ => True | _ => False) := by cbv
    cases same : root <;> simp only [same] at tag
    all_goals try cases tag
    rename_i entry body depth ordinary
    cases bodyShape : body <;> simp only [bodyShape] at tag
    all_goals try cases tag
    exact ⟨_,_,_,_,_,_,_,rfl⟩
  obtain ⟨entry,bodyEntry,originals,level,free,depth,ordinary,shape⟩ := shape
  have known := available
  have noFree := closed
  have literal := head
  rw [shape] at known noFree literal
  obtain ⟨keeps,_,_,_,rows⟩ := SourceCurrentRecursiveHeadUnionRows.actual
    entry bodyEntry originals level free depth ordinary heap initial_ready known noFree made.1 made.2 literal
  have retained := rows
  obtain ⟨unfolded,middle,outputs,memberAfter,called,calls,memberKeeps,memberGrowth,growth,paired,expansions,origins⟩ := rows
  have sourceIndex : originals[0]? = some source := by
    have computed : (match root with | .mu _ (.union _ members _ _) _ _ => members[0]? | _ => none) = some source := by cbv
    simpa only [shape] using computed
  obtain ⟨output,outputIndex,warm⟩ := paired_forward paired source 0 sourceIndex
  have exactEnvironment : selfEnvironment entry (.union bodyEntry originals level free) depth ordinary = environment := by
    simp only [environment,shape]
  rw [exactEnvironment] at warm expansions
  have same : sourceValue = output := by simp only [sourceValue,sourceRun,warm]
  subst output
  have positive : (nodeEdges sourceValue)[0]? = some chosenRow := by cbv
  have origin : MergedFreshOrdinaryGraph.Origin made.2 [sourceValue] chosenRow :=
    ⟨sourceValue,.seed List.mem_cons_self,List.mem_of_getElem? positive⟩
  have originalRows := expansions 0 source sourceValue sourceIndex outputIndex chosenRow origin
  refine ⟨built_done,head,keeps,?_,?_,?_,?_,?_,originalRows,
    entry,bodyEntry,originals,level,free,depth,ordinary,shape,retained⟩
  · intro falseClosed
    have opened : source.free.isEmpty = false := by cbv
    rw [falseClosed] at opened
    cases opened
  · cbv
  · cbv
  · cbv
  · cbv

/-- An actual union-body Head exposes a row from its open original node alternative. -/
theorem open_node_alternative :
    built = .done root heap ∧ Head root heap made.1 made.2 ∧ Keeps heap made.2 ∧
    source.free ≠ [] ∧ (match source with | .node .. => True | _ => False) ∧
    (nodeEdges made.1)[0]? = some chosenRow ∧ chosenRow.entry.key.constraint = selected ∧
    chosenRow.children.length = 2 ∧
    SourceCurrentRecursiveHeadUnionRows.MemberRows environment made.2 source chosenRow ∧
    ∃ (entry bodyEntry : Interned InternedBinderProtocol.NodeKey) (originals : List (Value Symbol Guard))
      (level : Nat) (free : List InternedBinderProtocol.Reference) (depth ordinary : Value Symbol Guard),
      root = .mu entry (.union bodyEntry originals level free) depth ordinary ∧
      SourceCurrentRecursiveHeadUnionRows.Rows entry bodyEntry originals level free depth ordinary heap made.1 made.2 := witness

end MicroCFTA.RecursiveHeadUnionKernels
