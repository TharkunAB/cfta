from pathlib import Path
h=Path(__file__).resolve().parent
s=Path('/tmp/mcfta-native-original-publication-trace-fixture/publication-trace-kernels-verify.py').read_text()
s=s.replace("PREFIX='publication-trace-kernels'","PREFIX='captured-node-rows-kernels'")
s=s.replace('OriginalPublicationTraceFixture.actual_strict_publication_order','OriginalCapturedNodeRowsFixture.actual_initial_captured_node_row')
s=s.replace('f6d3b7cd18c99580e7930f11099eab4014f6e61725f969f73db896ffe684e7cf','721138d4a0ab8a882527ed764e707695173bcf6a1699d470a450e070da89b90d')
s=s.replace('b18623e71434a2cf847869e098d7ff7990ab57f2f9458d4d7aa753c4ff81794e','2ab4a9747e277c5ff21d2a1971e4c625fb587ce1530390f655405ba4e9697eb4')
s=s.replace('4269eff77ca39081f7ef89829cee433e4255459acf1b0419f0053dcd3885ddf4','73a58a83d3c46233c245f10be1f301649626d7bb50149a19d02a821c399c0d51')
start=s.index(" assert source.count('SourceCurrentNativeOriginalPublicationTrace.build_trace_writers")
end=s.index(" printer=(HERE/(PREFIX+'-public.lean')).read_text()",start)
s=s[:start]+''' assert source.count('SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows expression root request fuel before current')==1
 for forbidden in ['SourceCurrentNativeOriginalCapturedMuRows.capture_source','SourceCurrentNativeOriginalObservedTerminals.of_observed','SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins','SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions','SourceCurrentNativeOriginalPublicationTrace.build_trace_writers']:
  assert forbidden not in source,forbidden
 assert 'slot_lookup' not in source
 private_type=source.split('private theorem checked_witness :\\n',1)[1].split(' := by\\n',1)[0]
 public_type=source.split('theorem actual_initial_captured_node_row :\\n',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 for token in [
  'InternedFreshOrdinaryConstruction.build expression [] empty = .done root heap',
  'SourceCurrentAllocatedNativePhysicalCompletion.Good before',
  'SourceCurrentNativeEdgeWriterGrowth.History before',
  '0 < fuel ∧ fuel < 128',
  'execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current',
  'Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current',
  'Available current.native.machine.heap siteBody',
  '(leaves siteBody)[1]? = some (.mu entry stored depth ordinary)',
  'heap.nodeRecords entry.key = some (.mu entry stored depth ordinary)',
  'current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary)',
  'Reference.interned entry.identity ∈ stored.free',
  'unfoldedRun = .done unfolded unfoldedHeap',
  'unfoldedRow.children = [.mu entry stored depth ordinary]',
  'storedRow.children = [.reference (.interned entry.identity)] ∧ unfoldedRow ≠ storedRow',
  '∃ path : Path empty before.native.machine.heap,',
  '(∀ (index : Nat) event, (events path)[index]? = some event',
  '(∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,',
  '∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,',
  '(events path)[outerIndex]? = some outer',
  'entry.key = outer.key ∧ Value.mu entry stored depth ordinary = outer.candidate',
  'entry = outer.entry ∧ stored = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary',
  '(∀ storedRow, RowAt stored storedRow →',
  'Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap)',
  '(∀ value after,',
  'current.native.machine.heap = .done value after',
  'row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish',
  '(∃ lexical start finish, Calls lexical storedRow.children start unfoldedRow.children finish)',
  'producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer',
  'SyntaxBound (Syntax.node expressions) producer.expression',
  'UnionDescent producer.expression (Syntax.node expressions)',
  'Context before inputs ∧ Reached expression [] (Syntax.node expressions) inputs before',
  'SourceRow (Syntax.node expressions) inputs before raw after storedRow',
  'build (Syntax.node expressions) inputs before = .done raw after',
  'buildEdges expressions inputs before = .done rows middle',
  'run (makeNode rows) middle = (raw,after)',
  '(nodeEdges raw)[outputIndex]? = some storedRow',
  '∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,',
  '∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,',
  'call.output = storedRow ∧ Grows after outer.afterBody',
  'Extends after.nodes.issued outer.afterBody.nodes.issued']:
  assert token in public_type,token
 assert public_type.count('∃ path : Path empty before.native.machine.heap,')==1
 assert public_type.count('∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,')==1
 assert public_type.count('∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,')==3
 assert public_type.count('∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,')==3
 for token in ['private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩',
               'private def before : Checked 1024 := ⟨initial 1024 machine,allocatedOps⟩',
               'private def control : Control Node := .code (requestNode request.domain request.left request.right)',
               'SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before',
               'outerPair siteBody siteNext built_done good history checked.trace available 1 entry stored depth ordinary found',
               'everyUnfold unfolded unfoldedHeap actual_unfold',
               'observedRows unfoldedRow (node_row (List.mem_of_getElem? unfolded_selected))',
               'have same := stored_rec_unique original inside (symbol.symm.trans unfolded_fields.1)',
               'exact False.elim (rows_distinct unchanged)',
               'inside,symbol,guard,arity,actualCalls,nodeFacts⟩',
               'have retained := prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1',
               'rw [missing] at retained']:
  assert token in source,token
 previous=(HERE/'inputs/prior-terminal-kernels.lean').read_text()
 assert digest(previous.encode())=='65157a032cc06f392ea577818ad4857740dea4f3453eff39e83742b7d3c67e94'
 current_helpers=source.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem checked_witness :',1)[0].strip()
 previous_helpers=previous.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem checked_witness :',1)[0].strip()
 assert current_helpers==previous_helpers
''' + s[end:]
s=s.replace('==1155998','==2105277')
s=s.replace("assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']","assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']\n assert selected['initial_branch_forced'] and selected['nonidentity_unfold_calls']\n assert selected['leaves_occurrence']==1 and selected['encode_slot_claim'] is False")
(h/'captured-node-rows-kernels-verify.py').write_text(s)
