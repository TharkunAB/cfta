import MicroCFTA.SourceCurrentStoredMuRetainedAlignment
import MicroCFTA.EqualityLeafProjectionPhysical
import MicroCFTA.InternedFlatProbeCosts

/-!
# Surviving rows of actual Mu callback nodes

Both callback outputs retain a surviving row at the same source index.
The paired row calls retain full fields and ordered child executions.
Children can contain nested Mu values. Their nonempty values need not agree.
-/
namespace MicroCFTA.SourceCurrentPublicationNodeRowSurvival
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedFacts InternedNestedProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext (Context)
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredMuRetainedAlignment (RowCall)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A selected row retains both actual source schedules and a surviving paired row. -/
def Paired (expressions : List (EdgeSyntax Symbol Guard)) (captures : List (Value Symbol Guard))
    (firstName secondName : Reference) (before after later final reader : State Symbol Guard)
    (firstValue secondValue : Value Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ (first : List (EdgeValue Symbol Guard)) (firstAfter : State Symbol Guard)
    (second : List (EdgeValue Symbol Guard)) (secondAfter : State Symbol Guard)
    (index : Nat) (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (left : RowCall expressions (.reference firstName :: captures) before first firstAfter reader
      index symbol guard children)
    (right : RowCall expressions (.reference secondName :: captures) later second secondAfter reader
      index symbol guard children),
    buildEdges expressions (.reference firstName :: captures) before = .done first firstAfter ∧
    run (makeNode first) firstAfter = (firstValue,after) ∧
    buildEdges expressions (.reference secondName :: captures) later = .done second secondAfter ∧
    run (makeNode second) secondAfter = (secondValue,final) ∧
    right.output = row ∧ left.output ∈ InternedEdgeResidency.nodeEdges firstValue ∧
    left.output.entry.key.symbol = row.entry.key.symbol ∧
    left.output.entry.key.constraint = row.entry.key.constraint ∧
    All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) left.values right.values ∧
    left.output.children.any (fun value => value.referenceOf == .empty) = false ∧
    right.output.children.any (fun value => value.referenceOf == .empty) = false

private theorem rows_length (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (outputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : buildEdges expressions environment before = .done outputs after) :
    expressions.length = outputs.length := by
  induction expressions generalizing before outputs with
  | nil =>
      simp only [buildEdges,Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      rfl
  | cons expression expressions ih =>
      cases expression with
      | mk symbol guard children =>
        cases child : buildMany children environment before with
        | pending key state => simp only [buildEdges,child,Outcome.bind] at actual; cases actual
        | done values middle =>
          let edge := run (makeEdge symbol guard values) middle
          cases rest : buildEdges expressions environment edge.2 with
          | pending key state =>
              simp only [buildEdges,child,Outcome.bind,work] at actual
              change (buildEdges expressions environment edge.2).bind _ = _ at actual
              simp only [rest,Outcome.bind] at actual
              cases actual
          | done tail final =>
              simp only [buildEdges,child,Outcome.bind,work] at actual
              change (buildEdges expressions environment edge.2).bind _ = _ at actual
              simp only [rest,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,rfl⟩ := actual
              simp only [List.length_cons,ih edge.2 tail rest]

private theorem node_parts (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (value : Value Symbol Guard) (actual : build (.node expressions) environment before = .done value after) :
    ∃ rows middle, buildEdges expressions environment before = .done rows middle ∧
      run (makeNode rows) middle = (value,after) := by
  cases called : buildEdges expressions environment before with
  | pending key state => simp only [build,called,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have same := Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)
      exact ⟨rows,middle,rfl,Prod.ext same.1 same.2⟩

/-- Actual node callbacks pair each selected row with a surviving row from the same source position. -/
theorem node (expressions : List (EdgeSyntax Symbol Guard)) (captures : List (Value Symbol Guard))
    (firstName secondName : Reference) (before after later final reader : State Symbol Guard)
    (firstContext : Context before (.reference firstName :: captures))
    (secondContext : Context later (.reference secondName :: captures))
    (firstValue secondValue : Value Symbol Guard)
    (called : build (.node expressions) (.reference firstName :: captures) before = .done firstValue after)
    (other : build (.node expressions) (.reference secondName :: captures) later = .done secondValue final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (row : EdgeValue Symbol Guard) (selected : row ∈ InternedEdgeResidency.nodeEdges secondValue) :
    Paired expressions captures firstName secondName before after later final reader firstValue secondValue row := by
  obtain ⟨first,firstAfter,firstDone,firstMade⟩ := node_parts expressions _ before after firstValue called
  obtain ⟨second,secondAfter,secondDone,secondMade⟩ := node_parts expressions _ later final secondValue other
  have firstChecked := InternedFreshOrdinaryFacts.buildEdges_verified expressions _ before firstContext.normal.facts firstContext.inputs
  have secondChecked := InternedFreshOrdinaryFacts.buildEdges_verified expressions _ later secondContext.normal.facts secondContext.inputs
  have firstFacts : Facts firstAfter := by simpa only [firstDone,Outcome.state] using firstChecked.facts
  have secondFacts : Facts secondAfter := by simpa only [secondDone,Outcome.state] using secondChecked.facts
  have firstEdges := firstChecked.result first firstAfter firstDone
  have secondEdges := secondChecked.result second secondAfter secondDone
  have firstRows := EqualityLeafProjectionPhysical.makeNode_edges first firstAfter
    firstFacts.coherent firstFacts.linked firstEdges
  have secondRows := EqualityLeafProjectionPhysical.makeNode_edges second secondAfter
    secondFacts.coherent secondFacts.linked secondEdges
  rw [firstMade] at firstRows
  rw [secondMade] at secondRows
  rw [secondRows] at selected
  obtain ⟨member,alive⟩ := (EqualityLeafProjectionPhysical.normalized_member secondAfter secondFacts.coherent
    second secondEdges row).mp selected
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
  have bounded : index < expressions.length := by
    rw [rows_length expressions _ later second secondAfter secondDone]
    exact (List.getElem?_eq_some_iff.mp found).1
  let expression := expressions[index]
  have source : expressions[index]? = some expression := List.getElem?_eq_getElem bounded
  cases shape : expression with
  | mk symbol guard children =>
    rw [shape] at source
    have firstRawGrowth : Grows firstAfter reader := grows_trans
      (by simpa only [firstMade] using (run_correct (makeNode first) firstAfter firstFacts.coherent.valid).2) firstGrowth
    have secondRawGrowth : Grows secondAfter reader := grows_trans
      (by simpa only [secondMade] using (run_correct (makeNode second) secondAfter secondFacts.coherent.valid).2) secondGrowth
    obtain ⟨left,right,paired,sameAlive⟩ := SourceCurrentStoredMuRetainedAlignment.paired_rows
      expressions captures firstName secondName before firstAfter later secondAfter reader
      firstContext secondContext first second firstDone secondDone firstRawGrowth secondRawGrowth
      index symbol guard children source
    have rightSame : right.output = row := Option.some.inj (right.selected.symm.trans found)
    have rightAlive : right.output.children.any (fun value => value.referenceOf == .empty) = false := by
      simpa only [rightSame,EqualityLeafProjectionPhysical.dead] using alive
    have leftAlive := sameAlive.trans rightAlive
    have leftMember : left.output ∈ InternedEdgeResidency.nodeEdges firstValue := by
      rw [firstRows]
      exact (EqualityLeafProjectionPhysical.normalized_member firstAfter firstFacts.coherent first firstEdges
        left.output).mpr ⟨List.mem_of_getElem? left.selected,leftAlive⟩
    exact ⟨first,firstAfter,second,secondAfter,index,symbol,guard,children,left,right,
      firstDone,firstMade,secondDone,secondMade,rightSame,leftMember,
      left.symbol_eq.trans ((rightSame ▸ right.symbol_eq).symm),
      left.guard_eq.trans ((rightSame ▸ right.guard_eq).symm),paired,leftAlive,rightAlive⟩

/-- An actual publication pairs each selected stored body row with its surviving ordinary callback row. -/
theorem publication (event : Publication (Symbol := Symbol) (Guard := Guard))
    (expressions : List (EdgeSyntax Symbol Guard)) (shape : event.expression = .node expressions)
    (row : EdgeValue Symbol Guard) (selected : row ∈ InternedEdgeResidency.nodeEdges event.body) :
    Paired expressions event.environment (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity)
      event.afterDepth event.cut event.allocated event.afterBody event.afterBody event.ordinary event.body row := by
  obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have ordinaryInputs := (depthContext.local (.uninterned (ordinaryLevel event.depth))
    (ordinary_available event.afterDepth (ordinaryLevel event.depth))).base
  have bodyInputs := (bodyContext.local (.interned event.entry.identity)
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2).base
  obtain ⟨rawOrdinary,ordinaryAfter,rawBody,bodyAfter,ordinaryDone,ordinaryFilter,bodyDone,bodyFilter,
    ordinaryGrowth,bodyGrowth,_depthContext,_bodyContext⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  rw [shape] at ordinaryDone bodyDone
  obtain ⟨first,firstAfter,firstDone,firstMade⟩ := node_parts expressions _ _ _ _ ordinaryDone
  obtain ⟨second,secondAfter,secondDone,secondMade⟩ := node_parts expressions _ _ _ _ bodyDone
  have firstChecked := InternedFreshOrdinaryFacts.buildEdges_verified expressions _ event.afterDepth ordinaryInputs.normal.facts ordinaryInputs.inputs
  have secondChecked := InternedFreshOrdinaryFacts.buildEdges_verified expressions _ event.allocated bodyInputs.normal.facts bodyInputs.inputs
  have firstFacts : Facts firstAfter := by simpa only [firstDone,Outcome.state] using firstChecked.facts
  have secondFacts : Facts secondAfter := by simpa only [secondDone,Outcome.state] using secondChecked.facts
  have firstFilter := InternedFlatProbeCosts.makeNode_filter (.uninterned (ordinaryLevel event.depth))
    first firstAfter firstFacts.coherent firstFacts.linked (firstChecked.result first firstAfter firstDone)
  have secondFilter := InternedFlatProbeCosts.makeNode_filter (.interned event.entry.identity)
    second secondAfter secondFacts.coherent secondFacts.linked (secondChecked.result second secondAfter secondDone)
  rw [firstMade] at firstFilter
  rw [secondMade] at secondFilter
  rw [firstFilter,run] at ordinaryFilter
  rw [secondFilter,run] at bodyFilter
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj ordinaryFilter
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj bodyFilter
  exact node expressions event.environment _ _ _ _ _ _ _ ordinaryInputs bodyInputs _ _
    ordinaryDone bodyDone ordinaryGrowth (grows_refl _) row selected

end MicroCFTA.SourceCurrentPublicationNodeRowSurvival
