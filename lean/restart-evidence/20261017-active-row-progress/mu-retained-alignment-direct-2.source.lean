import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentNativeNormalizedComparison
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Indexed row survival in actual source callbacks

The ordinary probe and reserved body execute the same source rows. Their
ordered children have the same physical empty tests, including nested Mu
children. The result does not compare the nonempty child values or Mu atoms.
-/
namespace MicroCFTA.SourceCurrentStoredMuRetainedAlignment
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedNestedFacts
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (Publication)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem empty_same (expression : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (firstName secondName : Reference) (before after later final : State Symbol Guard)
    (firstContext : Context before (.reference firstName :: captures))
    (secondContext : Context later (.reference secondName :: captures))
    (first second : Value Symbol Guard)
    (called : build expression (.reference firstName :: captures) before = .done first after)
    (other : build expression (.reference secondName :: captures) later = .done second final) :
    (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
  rw [InternedRecordDepthSource.source_empty expression _ before firstContext first after called,
    InternedRecordDepthSource.source_empty expression _ later secondContext second final other]
  let inputs : List (Sum (Value Symbol Guard) Unit) := .inr () :: captures.map Sum.inl
  have left := SourceCurrentNativeNormalizedComparison.instantiated expression inputs (fun _ => firstName)
  have right := SourceCurrentNativeNormalizedComparison.instantiated expression inputs (fun _ => secondName)
  have actualInputs (name : Reference) :
      inputs.map (InternedFreshOrdinaryLiveInputs.input (fun _ => name)) = .reference name :: captures := by
    simp [inputs, InternedFreshOrdinaryLiveInputs.input, List.map_map, Function.comp_def]
  rw [actualInputs] at left right
  rw [left, right, InternedDepthSemantics.isEmpty_map, InternedDepthSemantics.isEmpty_map]

private theorem many_empty (expressions : List (Syntax Symbol Guard)) (captures : List (Value Symbol Guard))
    (firstName secondName : Reference) (before after later final : State Symbol Guard)
    (firstContext : Context before (.reference firstName :: captures))
    (secondContext : Context later (.reference secondName :: captures))
    (first second : List (Value Symbol Guard))
    (called : buildMany expressions (.reference firstName :: captures) before = .done first after)
    (other : buildMany expressions (.reference secondName :: captures) later = .done second final) :
    All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second := by
  induction expressions generalizing before later first second with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at called other
      obtain ⟨rfl,rfl⟩ := called
      obtain ⟨rfl,rfl⟩ := other
      exact .nil
  | cons expression expressions ih =>
      cases one : build expression (.reference firstName :: captures) before with
      | pending key state => simp only [buildMany,one,Outcome.bind] at called; cases called
      | done value middle =>
        cases two : build expression (.reference secondName :: captures) later with
        | pending key state => simp only [buildMany,two,Outcome.bind] at other; cases other
        | done next nextHeap =>
          cases tail : buildMany expressions (.reference firstName :: captures) middle with
          | pending key state => simp only [buildMany,one,tail,Outcome.bind] at called; cases called
          | done values last =>
            cases rest : buildMany expressions (.reference secondName :: captures) nextHeap with
            | pending key state => simp only [buildMany,two,rest,Outcome.bind] at other; cases other
            | done results lastHeap =>
              simp only [buildMany,one,tail,Outcome.bind,Outcome.done.injEq] at called
              simp only [buildMany,two,rest,Outcome.bind,Outcome.done.injEq] at other
              obtain ⟨rfl,rfl⟩ := called
              obtain ⟨rfl,rfl⟩ := other
              have middleContext : Context middle (.reference firstName :: captures) := by
                simpa only [one,Outcome.state] using firstContext.build expression
              have nextContext : Context nextHeap (.reference secondName :: captures) := by
                simpa only [two,Outcome.state] using secondContext.build expression
              exact .cons (empty_same expression captures firstName secondName before middle later nextHeap
                firstContext secondContext value next one two)
                (ih middle nextHeap middleContext nextContext values results tail rest)

/-- One source row retains its exact prefix, ordered children, full fields, and suffix. -/
structure RowCall (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (outputs : List (EdgeValue Symbol Guard)) (after reader : State Symbol Guard)
    (index : Nat) (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard)) where
  /-- The row call starts after this exact prefix. -/
  current : State Symbol Guard
  /-- The children return this heap before edge allocation. -/
  middle : State Symbol Guard
  /-- The edge allocation returns this heap before the suffix. -/
  next : State Symbol Guard
  /-- The children return these complete records in source order. -/
  values : List (Value Symbol Guard)
  /-- The actual edge allocation returns this complete row. -/
  output : EdgeValue Symbol Guard
  /-- The original row occupies this source position. -/
  source : expressions[index]? = some (.mk symbol guard children)
  /-- The returned row occupies the same position before node normalization. -/
  selected : outputs[index]? = some output
  /-- The original prefix produces the actual row entry heap. -/
  earlier : buildEdges (expressions.take index) environment before = .done (outputs.take index) current
  /-- The original ordered children execute at that entry heap. -/
  called : buildMany children environment current = .done values middle
  /-- The row allocation uses its complete original symbol and guard. -/
  made : run (makeEdge symbol guard values) middle = (output,next)
  /-- The remaining rows execute from that allocation's actual return heap. -/
  suffix : buildEdges (expressions.drop (index + 1)) environment next = .done (outputs.drop (index + 1)) after
  /-- The actual child entry retains the complete source context. -/
  context : Context current environment
  /-- The output retains its complete source symbol. -/
  symbol_eq : output.entry.key.symbol = symbol
  /-- The output retains its complete source guard. -/
  guard_eq : output.entry.key.constraint = guard
  /-- The output retains all actual ordered child values. -/
  children_eq : output.children = values
  /-- The row entry heap grows into the common reader. -/
  current_growth : Grows current reader
  /-- The child return heap grows into the common reader. -/
  middle_growth : Grows middle reader
  /-- The row return heap grows into the common reader. -/
  next_growth : Grows next reader

private theorem row_call (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before environment)
    (outputs : List (EdgeValue Symbol Guard))
    (actual : buildEdges expressions environment before = .done outputs after)
    (growth : Grows after reader) (index : Nat) (symbol : Symbol) (guard : Guard)
    (children : List (Syntax Symbol Guard)) (found : expressions[index]? = some (.mk symbol guard children)) :
    Nonempty (RowCall expressions environment before outputs after reader index symbol guard children) := by
  induction expressions generalizing before outputs index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons expression expressions ih =>
    cases expression with
    | mk ownSymbol ownGuard ownChildren =>
      cases childDone : buildMany ownChildren environment before with
      | pending key state => simp only [buildEdges,childDone,Outcome.bind] at actual; cases actual
      | done values middle =>
        let made := run (makeEdge ownSymbol ownGuard values) middle
        cases tail : buildEdges expressions environment made.2 with
        | pending key state =>
            simp only [buildEdges,childDone,Outcome.bind,work] at actual
            change (buildEdges expressions environment made.2).bind _ = _ at actual
            simp only [tail,Outcome.bind] at actual
            cases actual
        | done remaining last =>
          simp only [buildEdges,childDone,Outcome.bind,work] at actual
          change (buildEdges expressions environment made.2).bind _ = _ at actual
          simp only [tail,Outcome.bind,Outcome.done.injEq] at actual
          obtain ⟨rfl,rfl⟩ := actual
          have childChecked := buildMany_verified ownChildren environment before context.normal.facts context.inputs
          have middleContext : Context middle environment := by
            simpa only [childDone,Outcome.state] using context.many ownChildren
          have childrenAvailable := childChecked.result values middle childDone
          have edgeChecked := InternedNestedFacts.edge_verified ownSymbol ownGuard values middle
            middleContext.normal.facts childrenAvailable
          have nextContext : Context made.2 environment := middleContext.edge ownSymbol ownGuard values childrenAvailable
          have tailChecked := buildEdges_verified expressions environment made.2 nextContext.normal.facts nextContext.inputs
          have nextGrowth : Grows made.2 reader := grows_trans (by simpa only [tail,Outcome.state] using tailChecked.growth) growth
          have middleGrowth : Grows middle reader := grows_trans edgeChecked.growth nextGrowth
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq,EdgeSyntax.mk.injEq] at found
            obtain ⟨rfl,rfl,rfl⟩ := found
            have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleContext.normal.facts
              ownSymbol ownGuard values childrenAvailable
            exact ⟨⟨before,middle,made.2,values,made.1,rfl,rfl,rfl,childDone,rfl,tail,
              context,fields.1,fields.2.1,fields.2.2,
              grows_trans (by simpa only [childDone,Outcome.state] using childChecked.growth) middleGrowth,
              middleGrowth,nextGrowth⟩⟩
          | succ index =>
            obtain ⟨row⟩ := ih made.2 nextContext remaining tail index found
            refine ⟨{row with source := found, selected := row.selected, earlier := ?_, suffix := ?_}⟩
            · simp only [List.take_succ_cons,buildEdges,childDone,Outcome.bind,work]
              exact congrArg (fun result => result.bind (fun rows final => .done (made.1 :: rows) final)) row.earlier
            · simpa only [List.drop_succ_cons,Nat.add_assoc] using row.suffix

/-- Both actual row schedules have equal ordered child-empty tests at each source index. -/
theorem paired_rows (expressions : List (EdgeSyntax Symbol Guard)) (captures : List (Value Symbol Guard))
    (firstName secondName : Reference) (before after later final reader : State Symbol Guard)
    (firstContext : Context before (.reference firstName :: captures))
    (secondContext : Context later (.reference secondName :: captures))
    (first second : List (EdgeValue Symbol Guard))
    (called : buildEdges expressions (.reference firstName :: captures) before = .done first after)
    (other : buildEdges expressions (.reference secondName :: captures) later = .done second final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (index : Nat) (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (found : expressions[index]? = some (.mk symbol guard children)) :
    ∃ (left : RowCall expressions (.reference firstName :: captures) before first after reader index symbol guard children)
      (right : RowCall expressions (.reference secondName :: captures) later second final reader index symbol guard children),
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) left.values right.values ∧
      left.output.children.any (fun value => value.referenceOf == .empty) =
        right.output.children.any (fun value => value.referenceOf == .empty) := by
  obtain ⟨left⟩ := row_call expressions _ before after reader firstContext first called firstGrowth index symbol guard children found
  obtain ⟨right⟩ := row_call expressions _ later final reader secondContext second other secondGrowth index symbol guard children found
  have paired := many_empty children captures firstName secondName left.current left.middle right.current right.middle
    left.context right.context left.values right.values left.called right.called
  refine ⟨left,right,paired,?_⟩
  rw [left.children_eq,right.children_eq]
  induction paired with
  | nil => rfl
  | cons same _ ih => simp only [List.any_cons,same,ih]

/-- An actual node-body publication produces both row schedules and their survival agreement. -/
theorem publication_rows (event : Publication (Symbol := Symbol) (Guard := Guard))
    (expressions : List (EdgeSyntax Symbol Guard)) (node : event.expression = .node expressions) :
    ∃ rawOrdinary ordinaryAfter rawBody bodyAfter first firstAfter second secondAfter,
      build (.node expressions) (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawOrdinary ordinaryAfter ∧
      build (.node expressions) (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawBody bodyAfter ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) ordinaryAfter = (event.ordinary,event.cut) ∧
      run (withoutSelfReference (.interned event.entry.identity) rawBody) bodyAfter = (event.body,event.afterBody) ∧
      buildEdges expressions (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done first firstAfter ∧
      run (makeNode first) firstAfter = (rawOrdinary,ordinaryAfter) ∧
      buildEdges expressions (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done second secondAfter ∧
      run (makeNode second) secondAfter = (rawBody,bodyAfter) ∧
      ∀ index symbol guard children, expressions[index]? = some (.mk symbol guard children) →
        ∃ (left : RowCall expressions (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
            event.afterDepth first firstAfter event.afterBody index symbol guard children)
          (right : RowCall expressions (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated second secondAfter event.afterBody index symbol guard children),
          All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) left.values right.values ∧
          left.output.children.any (fun value => value.referenceOf == .empty) =
            right.output.children.any (fun value => value.referenceOf == .empty) := by
  obtain ⟨rawOrdinary,ordinaryAfter,rawBody,bodyAfter,ordinaryDone,ordinaryFilter,bodyDone,bodyFilter,
    ordinaryGrowth,bodyGrowth,ordinaryContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  rw [node] at ordinaryDone bodyDone
  cases firstDone : buildEdges expressions (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment) event.afterDepth with
  | pending key state => simp only [build,firstDone,Outcome.bind] at ordinaryDone; cases ordinaryDone
  | done first firstAfter =>
    cases secondDone : buildEdges expressions (.reference (.interned event.entry.identity) :: event.environment) event.allocated with
    | pending key state => simp only [build,secondDone,Outcome.bind] at bodyDone; cases bodyDone
    | done second secondAfter =>
      have firstMade : run (makeNode first) firstAfter = (rawOrdinary,ordinaryAfter) := by
        apply Prod.ext
        · exact (Outcome.done.inj (by simpa only [build,firstDone,Outcome.bind,work] using ordinaryDone)).1
        · exact (Outcome.done.inj (by simpa only [build,firstDone,Outcome.bind,work] using ordinaryDone)).2
      have secondMade : run (makeNode second) secondAfter = (rawBody,bodyAfter) := by
        apply Prod.ext
        · exact (Outcome.done.inj (by simpa only [build,secondDone,Outcome.bind,work] using bodyDone)).1
        · exact (Outcome.done.inj (by simpa only [build,secondDone,Outcome.bind,work] using bodyDone)).2
      have ordinaryInputs := ordinaryContext.base.local (.uninterned (ordinaryLevel event.depth))
        (InternedNestedProvenance.ordinary_available _ _)
      have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
      have bodyInputs := bodyContext.base.local (.interned event.entry.identity)
        (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
          cutContext.base.normal.facts.cached).2
      have firstFacts : Facts firstAfter := by
        simpa only [firstDone,Outcome.state] using
          (buildEdges_verified expressions _ event.afterDepth ordinaryInputs.normal.facts ordinaryInputs.inputs).facts
      have secondFacts : Facts secondAfter := by
        simpa only [secondDone,Outcome.state] using
          (buildEdges_verified expressions _ event.allocated bodyInputs.normal.facts bodyInputs.inputs).facts
      have firstGrowth : Grows firstAfter event.afterBody := grows_trans
        (by simpa only [firstMade] using (run_correct (makeNode first) firstAfter firstFacts.coherent.valid).2) ordinaryGrowth
      have secondGrowth : Grows secondAfter event.afterBody := grows_trans
        (by simpa only [secondMade] using (run_correct (makeNode second) secondAfter secondFacts.coherent.valid).2) bodyGrowth
      refine ⟨rawOrdinary,ordinaryAfter,rawBody,bodyAfter,first,firstAfter,second,secondAfter,
        ordinaryDone,bodyDone,ordinaryFilter,bodyFilter,firstDone,firstMade,secondDone,secondMade,?_⟩
      intro index symbol guard children found
      exact paired_rows expressions event.environment _ _ event.afterDepth firstAfter event.allocated secondAfter event.afterBody
        ordinaryInputs bodyInputs first second firstDone secondDone firstGrowth secondGrowth index symbol guard children found

end MicroCFTA.SourceCurrentStoredMuRetainedAlignment
