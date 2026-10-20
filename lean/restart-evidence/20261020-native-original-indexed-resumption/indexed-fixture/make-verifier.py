from pathlib import Path
h=Path(__file__).resolve().parent
s=Path('/tmp/mcfta-native-original-publication-trace-fixture/publication-trace-kernels-verify.py').read_text()
s=s.replace("PREFIX='publication-trace-kernels'","PREFIX='indexed-resumption-kernels'")
s=s.replace("ATTEMPTS={PREFIX+'-direct-1':0,PREFIX+'-public-1':0}","ATTEMPTS={PREFIX+'-direct-1':1,PREFIX+'-direct-2':0,PREFIX+'-public-1':0}")
s=s.replace('OriginalPublicationTraceFixture.actual_strict_publication_order','OriginalIndexedResumptionFixture.actual_indexed_binder_resumption')
s=s.replace('f6d3b7cd18c99580e7930f11099eab4014f6e61725f969f73db896ffe684e7cf','d1e37939d0fe8e9b7ae0924665a08341ac7a195cd9e861764c04f9835c832818')
s=s.replace('b18623e71434a2cf847869e098d7ff7990ab57f2f9458d4d7aa753c4ff81794e','02932156e8189e5faad5dd107fb240657ac4851249c6c16a8c2b0d5b4e168aa4')
s=s.replace('4269eff77ca39081f7ef89829cee433e4255459acf1b0419f0053dcd3885ddf4','25a3d3a9bc737a7cba638e3ae57b80394e0a761c953b94544e90062f03aaeae3')
s=s.replace("assert usage['age_seconds']<120 and usage['remaining_percent']>1", "assert usage['age_seconds']<120 and usage['remaining_percent']>1\n  if code:assert \"unexpected token 'prefix'\" in (HERE/meta['log']).read_text()")
s=s.replace("PREFIX+'-direct-1.source.lean'","PREFIX+'-direct-2.source.lean'").replace("PREFIX+'-direct-1.log'","PREFIX+'-direct-2.log'")
start=s.index(" assert source.count('SourceCurrentNativeOriginalPublicationTrace.build_trace_writers")
end=s.index(" printer=(HERE/(PREFIX+'-public.lean')).read_text()",start)
s=s[:start]+''' assert source.count('SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions original root sourceHeap source_done')==1
 for forbidden in ['SourceCurrentNativeOriginalPublicationTrace.build_trace_writers','SourceCurrentNativeOriginalObservedResume.of_observed','SourceCurrentNativeOriginalUnionDescent.of_observed','SourceCurrentNativeOriginalBinderResume.resume']:
  assert forbidden not in source,forbidden
 private_type=source.split('private theorem checked_witness :\\n',1)[1].split(' := by\\n',1)[0]
 public_type=source.split('theorem actual_indexed_binder_resumption :\\n',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 for token in [
  'build (.binder false bodySyntax) [] empty = .done first firstHeap',
  'build original [] empty = .done sourceRoot sourceHeap',
  'firstHeap.nodeRecords (muKey firstDepth firstOrdinary) = some first',
  'outerEvent.body = first',
  'sourceHeap.nodeRecords outerEvent.key = some outerEvent.candidate',
  'RowAt firstBody tagRow','tagRow.children = []',
  '∃ path : Path empty sourceHeap,',
  '(∀ (index : Nat) event, (events path)[index]? = some event',
  '(∀ key entry body depth ordinary,',
  '(∀ (index : Nat) outer, (events path)[index]? = some outer',
  '∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _, ∃ raw rawAfter,',
  '(events path)[outerIndex]? = some outer',
  'outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate',
  'terminalExpression = Syntax.binder false bodySyntax ∧',
  'RowAt raw tagRow ∧',
  'terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary)',
  'outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary)',
  'terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody tagRow',
  '∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < outerIndex',
  '(events path)[earlierIndex]? = some earlier',
  'muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate',
  'earlier.afterBody.nodeRecords earlier.key = none',
  'Nonempty (Path earlier.allocated earlier.afterBody)',
  'Grows earlier.after outer.afterBody',
  'Extends earlier.after.nodes.issued outer.afterBody.nodes.issued',
  '∃ earlierRaw earlierRawAfter,',
  'earlier.allocated = .done earlierRaw earlierRawAfter',
  'RowAt earlierRaw tagRow ∧',
  'earlier.allocated earlierRaw earlierRawAfter tagRow ∧',
  '∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧']:
  assert token in public_type,token
 assert public_type.count('∃ path : Path empty sourceHeap,')==1
 assert public_type.count('∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,')==2
 assert public_type.count('terminalExpression = Syntax.binder false bodySyntax ∧')==1
 assert public_type.count('∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧')==2
 for token in ['obtain ⟨path,sites,finalWriters,precompletion,resumptions⟩ :=',
               'finalWriters event.key event.entry event.body event.depth event.ordinary outer_record',
               'resumptions outerIndex selectedEvent outerLookup',
               'suffix,suffixIssued,choice⟩ := rows row selectedInside',
               'have bodySame := (Value.mu.inj fullSame).2.1',
               'have targetSame := forced_terminal actualRoute nonunion kind',
               'have binderFacts := choice.resolve_left',
               'targetSame,binderFacts⟩']:
  assert token in source,token
 previous=(HERE/'inputs/prior-union-descent-kernels.lean').read_text()
 assert digest(previous.encode())=='04d8619d5ab9db5065c28c1ae38db7abe8fa0fd5713dd2eb8d7cfe470b91140c'
 current_helpers=source.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem outer_record :',1)[0].strip()
 previous_helpers=previous.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem source_context :',1)[0].strip()
 assert current_helpers==previous_helpers
 current_forcing=source.split('private theorem no_node_binder_path',1)[1].split('private theorem checked_witness :',1)[0].strip()
 previous_forcing=previous.split('private theorem no_node_binder_path',1)[1].split('private theorem checked_witness :',1)[0].strip()
 assert current_forcing==previous_forcing
''' + s[end:]
s=s.replace('==1155998','==3847621')
s=s.replace("assert selected['strict']==PREFIX+'-direct-1'","assert selected['strict']==PREFIX+'-direct-2'")
s=s.replace("selected['lean_jobs']==2 and selected['failed_attempts']==0","selected['lean_jobs']==3 and selected['failed_attempts']==1")
s=s.replace("assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']","assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']\n assert selected['source_forcing_helpers_byte_identical']")
s=s.replace('lean_jobs=2,failed_attempts=0','lean_jobs=3,failed_attempts=1')
(h/'indexed-resumption-kernels-verify.py').write_text(s)
