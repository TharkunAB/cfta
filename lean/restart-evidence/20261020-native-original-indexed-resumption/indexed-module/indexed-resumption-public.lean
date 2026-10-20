import MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
import MicroCFTA.SourceCurrentNativeOriginalUnionDescent

/-!
# Indexed original-source row resumptions

One completed source build fixes one publication trace.
Each callback keeps its exact source-union terminal.
A selected binder payload resumes at an earlier event in that trace.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalIndexedResumption
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request finish)
open InternedFreshOrdinaryConstruction (build buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback buildMany_verified)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeOriginalPublicationTrace (events)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentNativeOriginalUnionDescent (UnionDescent)
open SourceCurrentNativeOriginalObservedResume (SyntaxBound)
open InternedEdgeResidency (nodeEdges)

variable {Symbol Guard : Type}

private theorem terminal_suffix [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {fullRow : EdgeValue Symbol Guard}
    (context : Context before inputs)
    (reached : Reached root initial expression inputs before)
    (source : SourceRow expression inputs before raw after fullRow) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      UnionDescent expression terminalExpression ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached root initial terminalExpression terminalInputs terminalBefore ∧
      sizeOf terminalExpression ≤ sizeOf expression ∧
      Grows terminalAfter after ∧ Extends terminalAfter.nodes.issued after.nodes.issued := by
  have descend {currentExpression : Syntax Symbol Guard} {currentInputs : List (Value Symbol Guard)}
      {start : State Symbol Guard} {value : Value Symbol Guard} {stop : State Symbol Guard}
      {row : EdgeValue Symbol Guard}
      (part : SourceRow currentExpression currentInputs start value stop row) :
      Context start currentInputs → Reached root initial currentExpression currentInputs start →
      ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
        SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
        UnionDescent currentExpression terminalExpression ∧
        (∀ members, terminalExpression ≠ Syntax.union members) ∧
        Context terminalBefore terminalInputs ∧
        Reached root initial terminalExpression terminalInputs terminalBefore ∧
        sizeOf terminalExpression ≤ sizeOf currentExpression ∧
        Grows terminalAfter stop ∧ Extends terminalAfter.nodes.issued stop.nodes.issued := by
    induction part with
    | @capture currentInputs state value row slot found inside =>
      intro currentContext currentReached
      refine ⟨.var slot,currentInputs,state,value,state,.capture found inside,.refl _,?_,
        currentContext,currentReached,Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
    | @node expressions currentInputs start value stop rows middle symbol guard children row
        sourceIndex outputIndex built made canonical call same =>
      intro currentContext currentReached
      refine ⟨.node expressions,currentInputs,start,value,stop,.node built made canonical call same,.refl _,?_,
        currentContext,currentReached,Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
    | @union expressions currentInputs start value stop values middle member memberValue current next row
        index built made syntaxSelected valueSelected earlier memberContext called suffix nested ih =>
      intro currentContext currentReached
      have earlierFacts := buildMany_verified (expressions.take index) currentInputs start
        currentContext.base.normal.facts currentContext.base.inputs
      have earlierGrowth : Grows start current := by
        simpa only [earlier,Outcome.state] using earlierFacts.growth
      have memberReached : Reached root initial member currentInputs current :=
        (currentReached.union (List.mem_of_getElem? syntaxSelected)).grows earlierGrowth
      obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
        terminalSource,terminalDescent,nonunion,terminalContext,terminalReached,terminalBound,terminalGrowth,terminalIssued⟩ :=
        ih memberContext memberReached
      have returnContext : Context next currentInputs := by
        simpa only [called,Outcome.state] using memberContext.build member
      have suffixFacts := buildMany_verified (expressions.drop (index + 1)) currentInputs next
        returnContext.base.normal.facts returnContext.base.inputs
      have suffixGrowth : Grows next middle := by
        simpa only [suffix,Outcome.state] using suffixFacts.growth
      have suffixIssued : Extends next.nodes.issued middle.nodes.issued := by
        simpa only [suffix,Outcome.state] using suffixFacts.history
      have middleValid : Valid middle := by
        simpa only [suffix,Outcome.state] using suffixFacts.facts.coherent.valid
      have unionGrowth : Grows middle stop := by
        simpa only [made] using (InternedConstructorTemplates.run_correct (makeUnion values) middle middleValid).2
      have unionIssued : Extends middle.nodes.issued stop.nodes.issued := by
        simpa only [made] using InternedProbeProvenance.run_issued_extends (makeUnion values) middle middleValid
      have memberBound : sizeOf member ≤ sizeOf (Syntax.union expressions) := by
        have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? syntaxSelected)
        simp only [Syntax.union.sizeOf_spec]
        omega
      exact ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
        terminalSource,.member syntaxSelected terminalDescent,nonunion,terminalContext,terminalReached,Nat.le_trans terminalBound memberBound,
        grows_trans terminalGrowth (grows_trans suffixGrowth unionGrowth),
        extends_trans terminalIssued (extends_trans suffixIssued unionIssued)⟩
    | @binder smart body currentInputs start value stop depth afterDepth ordinary cut entry stored row
        depthDone ordinaryDone requested present returned inside =>
      intro currentContext currentReached
      refine ⟨.binder smart body,currentInputs,start,value,stop,
        .binder depthDone ordinaryDone requested present returned inside,.refl _,?_,currentContext,currentReached,
        Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
  exact descend source context reached


private theorem source_done [DecidableEq (EdgeKey Symbol Guard)]
    {expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {row : EdgeValue Symbol Guard} (source : SourceRow expression inputs before raw after row) :
    build expression inputs before = .done raw after := by
  cases source with
  | capture found _ => simp only [build,found,Option.getD_some]
  | node built made _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | union built made _ _ _ _ _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | @binder smart expression inputs before raw after depth afterDepth ordinary cut entry body row
      depthDone ordinaryDone requested _ _ _ =>
    simp only [build]
    change ((callback expression inputs .depth before).bind fun depth afterDepth =>
      (callback expression inputs (.uninterned (ordinaryLevel depth)) afterDepth).bind
        fun ordinary cut => request smart depth ordinary (callback expression inputs) cut) = .done raw after
    simpa only [depthDone,ordinaryDone,Outcome.bind] using requested

private theorem terminal_original [DecidableEq (EdgeKey Symbol Guard)]
    {original expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {fullRow : EdgeValue Symbol Guard}
    (context : Context before inputs)
    (reached : Reached original [] expression inputs before)
    (source : SourceRow expression inputs before raw after fullRow) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ rows, terminalExpression = Syntax.node rows) ∨
        ∃ smart body, terminalExpression = Syntax.binder smart body) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression expression ∧
      UnionDescent expression terminalExpression ∧
      Grows terminalAfter after ∧ Extends terminalAfter.nodes.issued after.nodes.issued := by
  obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,descent,nonunion,terminalContext,terminalReached,bound,growth,issued⟩ :=
    terminal_suffix context reached source
  have kind : (∃ rows, terminalExpression = Syntax.node rows) ∨
      ∃ smart body, terminalExpression = Syntax.binder smart body := by
    cases terminalSource with
    | capture found inside =>
      obtain ⟨crossings,path,_⟩ := terminalReached
      exact (SourceCurrentSourceCaptureOriginalSlots.empty_initial path _ _ found fullRow inside).elim
    | node => exact .inl ⟨_,rfl⟩
    | union => exact (nonunion _ rfl).elim
    | binder => exact .inr ⟨_,_,rfl⟩
  exact ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,source_done terminalSource,kind,nonunion,terminalContext,terminalReached,bound,descent,growth,issued⟩


private theorem callback_rows [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (original : Syntax Symbol Guard)
    (reached : Reached original [] (.binder event.smart event.expression) event.environment event.before) :
    ∃ raw rawAfter,
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached original [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧
      ∀ row, RowAt event.body row → RowAt raw row ∧
        SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated raw rawAfter row := by
  obtain ⟨raw,rawAfter,built,filtered⟩ := SourceCurrentNativeMuPublicationCallbacks.callback_raw
    event.expression event.environment (.interned event.entry.identity) event.allocated
    event.body event.afterBody event.bodyDone
  let crossing : InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard :=
    ⟨event.smart,event.expression,event.environment,event.before,.interned event.entry.identity,
      event.allocated,event.context.base,
      .fresh event.depth event.ordinary event.afterDepth event.cut
        event.depthDone event.ordinaryDone event.missing⟩
  have callbackReached : Reached original [] event.expression
      (.reference (.interned event.entry.identity) :: event.environment) event.allocated := reached.enter crossing
  obtain ⟨_,cutContext,allocatedContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut
      cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  have context := allocatedContext.local (.interned event.entry.identity) argument
  refine ⟨raw,rawAfter,built,filtered,context,callbackReached,?_⟩
  intro row inside
  obtain ⟨other,otherAfter,otherBuilt,_,_,_,rawRow,source⟩ :=
    SourceCurrentPublicationBodySourceRows.publication_body_origin event original [] reached row inside
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (built.symm.trans otherBuilt)
  exact ⟨rawRow,source⟩

section
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem binder_before (original : Syntax Symbol Guard) (traceAfter : State Symbol Guard)
    (path : Path empty traceAfter)
    (precompletion : ∀ (index : Nat) outer, (events path)[index]? = some outer →
      ∀ key entry body depth ordinary,
        outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
          Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
          key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
          earlier.afterBody.nodeRecords earlier.key = none ∧
          Nonempty (Path empty earlier.before) ∧
          Nonempty (Path earlier.before earlier.afterDepth) ∧
          Nonempty (Path earlier.afterDepth earlier.cut) ∧
          Nonempty (Path earlier.allocated earlier.afterBody) ∧
          Grows earlier.after outer.afterBody ∧
          Extends earlier.after.nodes.issued outer.afterBody.nodes.issued)
    (index : Nat) (outer : @Publication Symbol Guard _)
    (selectedOuter : (events path)[index]? = some outer)
    (raw : Value Symbol Guard) (rawAfter : State Symbol Guard)
    (context : Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment))
    (built : build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
      outer.allocated = .done raw rawAfter)
    (filtered : run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter =
      (outer.body,outer.afterBody))
    (smart : Bool) (terminalExpression : Syntax Symbol Guard) (terminalInputs : List (Value Symbol Guard))
    (terminalBefore : State Symbol Guard) (terminalRaw : Value Symbol Guard)
    (terminalAfter : State Symbol Guard) (row : EdgeValue Symbol Guard)
    (terminal : SourceRow (.binder smart terminalExpression) terminalInputs terminalBefore terminalRaw terminalAfter row)
    (suffix : Grows terminalAfter rawAfter)
    (suffixIssued : Extends terminalAfter.nodes.issued rawAfter.nodes.issued) :
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalExpression terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalExpression terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalExpression terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < index ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued := by
  cases terminal with
  | @binder smart expression inputs before value after depth afterDepth ordinary cut entry storedBody row
      depthDone ordinaryDone requested selected returned inside =>
    have returnedContext : Context rawAfter
        (.reference (.interned outer.entry.identity) :: outer.environment) := by
      simpa only [built,Outcome.state] using context.build outer.expression
    have filterGrowth := (run_correct (withoutSelfReference (.interned outer.entry.identity) raw)
      rawAfter returnedContext.base.normal.facts.coherent.valid).2
    have filterIssued := run_issued_extends (withoutSelfReference (.interned outer.entry.identity) raw)
      rawAfter returnedContext.base.normal.facts.coherent.valid
    rw [filtered] at filterGrowth filterIssued
    have beforeGrowth : Grows terminalAfter outer.afterBody := grows_trans suffix filterGrowth
    have beforeIssued : Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued :=
      extends_trans suffixIssued filterIssued
    have present := beforeGrowth.nodeRecords (muKey depth ordinary) _ selected
    exact ⟨depth,afterDepth,ordinary,cut,entry,storedBody,depthDone,ordinaryDone,requested,
      selected,present,returned,inside,beforeGrowth,beforeIssued,
      precompletion index outer selectedOuter (muKey depth ordinary) entry storedBody depth ordinary present⟩

end

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem terminal_resume (original : Syntax Symbol Guard) (traceAfter : Heap)
    (path : Path empty traceAfter)
    (precompletion : ∀ (index : Nat) outer, (events path)[index]? = some outer →
      ∀ key entry body depth ordinary,
        outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
          Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
          key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
          earlier.afterBody.nodeRecords earlier.key = none ∧
          Nonempty (Path empty earlier.before) ∧
          Nonempty (Path earlier.before earlier.afterDepth) ∧
          Nonempty (Path earlier.afterDepth earlier.cut) ∧
          Nonempty (Path earlier.allocated earlier.afterBody) ∧
          Grows earlier.after outer.afterBody ∧
          Extends earlier.after.nodes.issued outer.afterBody.nodes.issued)
    (index : Nat) (outer : @Publication Symbol Guard _)
    (selectedOuter : (events path)[index]? = some outer)
    (raw : Node) (rawAfter : Heap)
    (context : Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment))
    (built : build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
      outer.allocated = .done raw rawAfter)
    (filtered : run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter = (outer.body,outer.afterBody))
    (callbackReached : Reached original [] outer.expression
      (.reference (.interned outer.entry.identity) :: outer.environment) outer.allocated)
    (row : EdgeValue Symbol Guard)
    (source : SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
      outer.allocated raw rawAfter row) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression outer.expression ∧
      UnionDescent outer.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < index ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued ∧
        ∃ earlierRaw earlierRawAfter,
          build earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated = .done earlierRaw earlierRawAfter ∧
          run (withoutSelfReference (.interned earlier.entry.identity) earlierRaw) earlierRawAfter =
            (earlier.body,earlier.afterBody) ∧
          Context earlier.allocated (.reference (.interned earlier.entry.identity) :: earlier.environment) ∧
          Reached original [] earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated ∧
          RowAt earlierRaw row ∧
          SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated earlierRaw earlierRawAfter row ∧
          ∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧
            SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
              earlier.allocated earlierRaw earlierRawAfter storedRow)) := by
  obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,done,kind,nonunion,terminalContext,terminalReached,bound,descent,suffix,suffixIssued⟩ :=
    terminal_original context callbackReached source
  refine ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,done,kind,nonunion,terminalContext,terminalReached,bound,descent,suffix,suffixIssued,?_⟩
  rcases kind with ⟨expressions,rfl⟩ | ⟨smart,terminalBody,rfl⟩
  · cases terminalSource with
    | @node expressions inputs before raw after rows middle symbol guard children row sourceIndex outputIndex
        builtRows made selected call same =>
      exact .inl ⟨_,_,_,_,_,_,_,_,rfl,builtRows,made,selected,call,same⟩
  · obtain ⟨depth,afterDepth,ordinary,cut,entry,storedBody,depthDone,ordinaryDone,requested,present,
      presentBefore,returned,inside,beforeGrowth,beforeIssued,earlierIndex,earlier,less,selectedEarlier,
      earlierReached,keySame,valueSame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued⟩ :=
      binder_before original traceAfter path precompletion index outer selectedOuter raw rawAfter
        context built filtered smart terminalBody terminalInputs terminalBefore terminalRaw terminalAfter
        row terminalSource suffix suffixIssued
    obtain ⟨earlierRaw,earlierRawAfter,earlierBuilt,earlierFiltered,earlierContext,earlierCallbackReached,earlierRows⟩ :=
      callback_rows earlier original earlierReached
    have bodySame : storedBody = earlier.body := (Value.mu.inj valueSame).2.1
    obtain ⟨rawRow,rawSource⟩ := earlierRows row (bodySame ▸ inside)
    refine .inr ⟨smart,terminalBody,rfl,depth,afterDepth,ordinary,cut,entry,storedBody,
      depthDone,ordinaryDone,requested,present,presentBefore,returned,inside,beforeGrowth,beforeIssued,
      earlierIndex,earlier,less,selectedEarlier,earlierReached,keySame,valueSame,missing,prefixPath,
      depthPath,ordinaryPath,bodyPath,growth,issued,earlierRaw,earlierRawAfter,earlierBuilt,earlierFiltered,
      earlierContext,earlierCallbackReached,rawRow,rawSource,?_⟩
    intro storedRow storedInside
    exact earlierRows storedRow (bodySame ▸ storedInside)

/-- One actual source trace fixes all stored-row terminals and their strictly earlier binder writers. -/
theorem build_row_resumptions (original : Syntax Symbol Guard) (sourceRoot : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done sourceRoot sourceHeap) :
    ∃ path : Path empty sourceHeap,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original [] (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path empty event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
      ∀ key entry body depth ordinary,
        outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
          Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
          key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
          earlier.afterBody.nodeRecords earlier.key = none ∧
          Nonempty (Path empty earlier.before) ∧
          Nonempty (Path earlier.before earlier.afterDepth) ∧
          Nonempty (Path earlier.afterDepth earlier.cut) ∧
          Nonempty (Path earlier.allocated earlier.afterBody) ∧
          Grows earlier.after outer.afterBody ∧
          Extends earlier.after.nodes.issued outer.afterBody.nodes.issued) ∧
      ∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∃ raw rawAfter,
          build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated = .done raw rawAfter ∧
          run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter = (outer.body,outer.afterBody) ∧
          Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment) ∧
          Reached original [] outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated ∧
          ∀ row, RowAt outer.body row → RowAt raw row ∧
            SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
              outer.allocated raw rawAfter row ∧
            ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression outer.expression ∧
      UnionDescent outer.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < index ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued ∧
        ∃ earlierRaw earlierRawAfter,
          build earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated = .done earlierRaw earlierRawAfter ∧
          run (withoutSelfReference (.interned earlier.entry.identity) earlierRaw) earlierRawAfter =
            (earlier.body,earlier.afterBody) ∧
          Context earlier.allocated (.reference (.interned earlier.entry.identity) :: earlier.environment) ∧
          Reached original [] earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated ∧
          RowAt earlierRaw row ∧
          SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated earlierRaw earlierRawAfter row ∧
          ∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧
            SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
              earlier.allocated earlierRaw earlierRawAfter storedRow)) := by
  obtain ⟨path,sites,finalWriters,precompletion⟩ :=
    SourceCurrentNativeOriginalPublicationTrace.build_trace_writers original [] empty
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key entry body depth ordinary impossible; cases impossible) sourceRoot sourceHeap sourceBuilt
  refine ⟨path,sites,finalWriters,precompletion,?_⟩
  intro index outer selectedOuter
  obtain ⟨raw,rawAfter,built,filtered,context,callbackReached,rows⟩ :=
    callback_rows outer original (sites index outer selectedOuter)
  refine ⟨raw,rawAfter,built,filtered,context,callbackReached,?_⟩
  intro row inside
  obtain ⟨rawRow,source⟩ := rows row inside
  exact ⟨rawRow,source,terminal_resume original sourceHeap path precompletion index outer selectedOuter
    raw rawAfter context built filtered callbackReached row source⟩

end MicroCFTA.SourceCurrentNativeOriginalIndexedResumption

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions
#print MicroCFTA.SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions
#print axioms MicroCFTA.SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions
