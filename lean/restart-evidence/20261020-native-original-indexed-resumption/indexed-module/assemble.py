from pathlib import Path
p=Path(__file__).resolve().parent
core=(p/'binder-before-snippet.lean.txt').read_text()
precomp=core.split('(precompletion : ',1)[1].split(')\n    (index : Nat)',1)[0]
core_result=core[core.index('    ∃ depth afterDepth ordinary cut entry storedBody,'):core.index(' := by\n')].replace('terminalExpression','terminalBody')
earlier_raw=''' ∧
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
              earlier.allocated earlierRaw earlierRawAfter storedRow'''
node='''(∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row)'''
terminal='''∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
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
      ('''+node+''' ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
'''+core_result+earlier_raw+'))'
private='''local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem terminal_resume (original : Syntax Symbol Guard) (traceAfter : Heap)
    (path : Path empty traceAfter)
    (precompletion : '''+precomp+''')
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
    '''+terminal+''' := by
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

'''
finalwriters='''∀ key entry body depth ordinary,
        sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path empty event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued'''
public='''/-- One actual source trace fixes all stored-row terminals and their strictly earlier binder writers. -/
theorem build_row_resumptions (original : Syntax Symbol Guard) (sourceRoot : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done sourceRoot sourceHeap) :
    ∃ path : Path empty sourceHeap,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original [] (.binder event.smart event.expression) event.environment event.before) ∧
      ('''+finalwriters+''') ∧
      ('''+precomp+''') ∧
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
            '''+terminal+''' := by
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
'''
source=(p/'header.lean.txt').read_text()+(p/'joint-helpers.lean.txt').read_text()+(p/'callback-rows.lean.txt').read_text()+'section\nvariable [DecidableEq (EdgeKey Symbol Guard)]\n\n'+core+'\nend\n\n'+private+public
(p/'binder-before-snippet.lean.txt').write_text(core)
(p/'public-producer.lean.txt').write_text(public)
(p/'SourceCurrentNativeOriginalIndexedResumption.lean').write_text(source)
