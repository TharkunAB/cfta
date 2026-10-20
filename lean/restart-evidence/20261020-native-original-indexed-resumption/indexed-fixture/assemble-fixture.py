from pathlib import Path
h=Path(__file__).resolve().parent
source=(h/'indexed-resumption-kernels.lean').read_text().split('-- The producer API',1)[0]
source=source.replace('open SourceCurrentNativeMuIssuedHistory (Path)','open SourceCurrentNativeMuIssuedHistory (Path)\nopen SourceCurrentNativeOriginalPublicationTrace (events)')
api=Path('/tmp/mcfta-native-original-indexed-resumption/public-producer.lean.txt').read_text()
conclusion=api.split('    ∃ path : Path empty sourceHeap,',1)[1].split(' := by\n',1)[0]
conclusion='    ∃ path : Path empty sourceHeap,'+conclusion
final_forall='      ∀ (index : Nat) outer, (events path)[index]? = some outer →\n        ∃ raw rawAfter,'
assert conclusion.count(final_forall)==1
conclusion=conclusion.replace(final_forall,final_forall.replace('      ∀','      (∀',1))
# The copied complete resumption clause stays inside one conjunction.
conclusion+=') ∧\n'
common=api.split('            ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,\n',1)[1].split('      ((∃ expressions rows middle,',1)[0]
binder=api.split('        (∃ smart terminalBody,\n          terminalExpression = Syntax.binder smart terminalBody ∧\n',1)[1].split(' := by\n',1)[0]
assert binder.endswith('))')
binder='      (∃ smart terminalBody,\n          terminalExpression = Syntax.binder smart terminalBody ∧\n'+binder[:-1]
# This last term includes the one remaining binder existential parenthesis.
explicit='''      ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _, ∃ raw rawAfter,
        (events path)[outerIndex]? = some outer ∧
        Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
        outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate ∧
        outer.afterBody.nodeRecords outer.key = none ∧
        Nonempty (Path empty outer.before) ∧
        Nonempty (Path outer.before outer.afterDepth) ∧
        Nonempty (Path outer.afterDepth outer.cut) ∧
        Nonempty (Path outer.allocated outer.afterBody) ∧
        Grows outer.after sourceHeap ∧ Extends outer.after.nodes.issued sourceHeap.nodes.issued ∧
        build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter = (outer.body,outer.afterBody) ∧
        Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment) ∧
        Reached original [] outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated ∧
        RowAt raw tagRow ∧
        SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated raw rawAfter tagRow ∧
        ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
'''
explicit+=common.replace(' row',' tagRow')
explicit+='      terminalExpression = Syntax.binder false bodySyntax ∧\n'
explicit+=binder.replace(' row',' tagRow').replace('earlierIndex < index','earlierIndex < outerIndex')
trace=Path('/tmp/mcfta-native-original-publication-trace-fixture/publication-trace-kernels.lean').read_text()
lead=trace.split('private theorem checked_witness :\n',1)[1].split('    ∃ path : Path empty sourceHeap,',1)[0]
claim=lead+conclusion+explicit
proof='''  obtain ⟨path,sites,finalWriters,precompletion,resumptions⟩ :=
    SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions original root sourceHeap source_done
  obtain ⟨outerIndex,selectedEvent,outerLookup,rooted,keySame,fullSame,missing,
    prefix,depthPath,ordinaryPath,bodyPath,growth,issued⟩ :=
    finalWriters event.key event.entry event.body event.depth event.ordinary outer_record
  have bodySame := (Value.mu.inj fullSame).2.1
  have selectedInside : RowAt selectedEvent.body row := by
    rw [← bodySame]
    exact outer_inside
  obtain ⟨observedRaw,observedAfter,built,filtered,context,reached,rows⟩ :=
    resumptions outerIndex selectedEvent outerLookup
  obtain ⟨rawRow,source,terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,terminalDone,kind,nonunion,terminalContext,terminalReached,bound,route,
    suffix,suffixIssued,choice⟩ := rows row selectedInside
  have outerExpression := fixed_outer_expression selectedEvent observedRaw observedAfter row rooted source filtered bodySame
  have actualRoute : UnionDescent outerBody terminalExpression := by simpa only [outerExpression] using route
  have targetSame := forced_terminal actualRoute nonunion kind
  have binderFacts := choice.resolve_left (by
    rintro ⟨expressions,rows,middle,sourceIndex,outputIndex,symbol,guard,children,equal,_⟩
    cases targetSame.symm.trans equal)
  refine ⟨nestedBody,original,firstMu,root,firstHeap,sourceHeap,event,firstEntry,firstBody,firstDepth,
    firstOrdinary,row,rfl,rfl,first_done,source_done,first_shape,?_,rfl,rfl,rfl,rfl,outer_shape,outer_done,
    nested_warm,outer_record,first_body_inside,row_fields.1,row_fields.2.1,row_fields.2.2,
    path,sites,finalWriters,precompletion,resumptions,
    outerIndex,selectedEvent,observedRaw,observedAfter,outerLookup,rooted,keySame,fullSame,missing,
    prefix,depthPath,ordinaryPath,bodyPath,growth,issued,built,filtered,context,reached,rawRow,source,
    terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,terminalSource,
    terminalDone,kind,nonunion,terminalContext,terminalReached,bound,route,suffix,suffixIssued,
    targetSame,binderFacts⟩
  simpa only [first_shape] using first_is_prior
'''
source+='private theorem checked_witness :\n'+claim+' := by\n'+proof
source+='''
/-- The same returned terminal resumes at a strict earlier indexed writer and its actual raw callback. -/
theorem actual_indexed_binder_resumption :
'''+claim+' := checked_witness\n\nend MicroCFTA.OriginalIndexedResumptionFixture\n'
(h/'indexed-resumption-kernels.lean').write_text(source)
print(len(source.splitlines()))
