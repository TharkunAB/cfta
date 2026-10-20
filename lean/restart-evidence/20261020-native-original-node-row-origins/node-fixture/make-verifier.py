from pathlib import Path
h=Path(__file__).resolve().parent
s=Path('/tmp/mcfta-native-original-publication-trace-fixture/publication-trace-kernels-verify.py').read_text()
s=s.replace("PREFIX='publication-trace-kernels'","PREFIX='node-row-origins-kernels'")
s=s.replace('OriginalPublicationTraceFixture.actual_strict_publication_order','OriginalNodeRowOriginsFixture.actual_strict_node_row_origin')
s=s.replace('f6d3b7cd18c99580e7930f11099eab4014f6e61725f969f73db896ffe684e7cf','9fcedfe8f4af9c2ed8641d933810e4b02878abedd0195bc8f597b1dc1e68e89c')
s=s.replace('b18623e71434a2cf847869e098d7ff7990ab57f2f9458d4d7aa753c4ff81794e','898fa1551a67bade1bb2eec2ce3d0c373bd652633ec7964d1fb5fb44634e805b')
s=s.replace('4269eff77ca39081f7ef89829cee433e4255459acf1b0419f0053dcd3885ddf4','77ebcd45a4f36f0118f175194ccf102bf9af2fb85173e80744a2e48dbeb6371d')
start=s.index(" assert source.count('SourceCurrentNativeOriginalPublicationTrace.build_trace_writers")
end=s.index(" printer=(HERE/(PREFIX+'-public.lean')).read_text()",start)
s=s[:start]+''' assert source.count('SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins original root sourceHeap source_done')==1
 for forbidden in ['SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions','SourceCurrentNativeOriginalPublicationTrace.build_trace_writers','SourceCurrentNativeOriginalObservedResume.of_observed','SourceCurrentNativeOriginalUnionDescent.of_observed','SourceCurrentNativeOriginalBinderResume.resume']:
  assert forbidden not in source,forbidden
 assert source.count('SourceCurrentPublicationBodySourceRows.publication_body_origin selectedEvent original [] rooted row selectedInside')==1
 private_type=source.split('private theorem checked_witness :\\n',1)[1].split(' := by\\n',1)[0]
 public_type=source.split('theorem actual_strict_node_row_origin :\\n',1)[1].split(' := checked_witness',1)[0]
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
  '∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,',
  '(events path)[outerIndex]? = some outer',
  'outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate',
  'outer.expression = Syntax.union [.var 0,.binder false bodySyntax]',
  'producerIndex < outerIndex ∧ producerIndex ≤ outerIndex',
  '(events path)[producerIndex]? = some producer',
  'SyntaxBound (Syntax.node expressions) producer.expression',
  'UnionDescent producer.expression (Syntax.node expressions)',
  'Context before inputs ∧ Reached original [] (Syntax.node expressions) inputs before',
  'SourceRow (Syntax.node expressions) inputs before raw after tagRow',
  'build (Syntax.node expressions) inputs before = .done raw after',
  'buildEdges expressions inputs before = .done rows middle',
  'run (makeNode rows) middle = (raw,after)',
  '(nodeEdges raw)[outputIndex]? = some tagRow',
  '∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,',
  '∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,',
  'call.output = tagRow ∧ Grows after outer.afterBody',
  'Extends after.nodes.issued outer.afterBody.nodes.issued']:
  assert token in public_type,token
 assert public_type.count('∃ path : Path empty sourceHeap,')==1
 assert public_type.count('∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,')==2
 assert public_type.count('producerIndex < outerIndex')==1
 assert public_type.count('∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,')==2
 for token in ['obtain ⟨path,sites,finalWriters,origins⟩ :=',
               'finalWriters event.key event.entry event.body event.depth event.ordinary outer_record',
               'have bodySame := (Value.mu.inj fullSame).2.1',
               'origins outerIndex selectedEvent outerLookup row selectedInside',
               'have strict : producerIndex < outerIndex := Nat.lt_of_le_of_ne producerBound',
               'have sameEvent : producer = selectedEvent := Option.some.inj (sameLookup.symm.trans outerLookup)',
               'simpa only [sameEvent,outerExpression] using nodeDescent',
               'exact no_node_descent expressions route',
               'canonical,call,callSame,nodeGrowth,nodeIssued⟩']:
  assert token in source,token
 previous=(HERE/'inputs/prior-indexed-resumption-kernels.lean').read_text()
 assert digest(previous.encode())=='d1e37939d0fe8e9b7ae0924665a08341ac7a195cd9e861764c04f9835c832818'
 current_helpers=source.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem outer_record :',1)[0].strip()
 previous_helpers=previous.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem outer_record :',1)[0].strip()
 assert current_helpers==previous_helpers
 current_forcing=source.split('private theorem no_node_binder_path',1)[1].split('private theorem no_node_descent',1)[0].strip()
 previous_forcing=previous.split('private theorem no_node_binder_path',1)[1].split('private theorem checked_witness :',1)[0].strip()
 assert current_forcing==previous_forcing
''' + s[end:]
s=s.replace('==1155998','==1468808')
s=s.replace("assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']","assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']\n assert selected['source_forcing_helpers_byte_identical']")
(h/'node-row-origins-kernels-verify.py').write_text(s)
