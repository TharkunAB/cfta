import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='captured-node-rows-kernels'
ATTEMPTS={PREFIX+'-direct-1':0,PREFIX+'-public-1':0}
NAME='MicroCFTA.OriginalCapturedNodeRowsFixture.actual_initial_captured_node_row'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='721138d4a0ab8a882527ed764e707695173bcf6a1699d470a450e070da89b90d'
PRINTER='2ab4a9747e277c5ff21d2a1971e4c625fb587ce1530390f655405ba4e9697eb4'
def digest(data):return hashlib.sha256(data).hexdigest()
def check(base,item):
 data=(base/item['path']).read_bytes()
 assert len(data)==item['bytes'],('bytes',item['path'])
 assert digest(data)==item['sha256'],('sha256',item['path'])
def main():
 parser=argparse.ArgumentParser()
 parser.add_argument('--root',type=Path,default=next((p for p in HERE.parents if (p/'lean/MicroCFTA').is_dir()),Path('/home/tritlo/Code/mcfta')))
 parser.add_argument('--live',action='store_true')
 args=parser.parse_args()
 manifest=json.loads((HERE/(PREFIX+'-manifest.json')).read_text())
 for item in manifest['files']:check(HERE,item)
 for item in manifest['sources']:
  check(HERE,dict(item,path=item['snapshot']))
  if args.live:check(args.root,item)
 assert manifest['sources']==json.loads((HERE/(PREFIX+'-source-pins.json')).read_text())['sources']
 assert manifest['sources'][0]['sha256']=='73a58a83d3c46233c245f10be1f301649626d7bb50149a19d02a821c399c0d51'
 assert not any(item['path']==PREFIX+'-peaks.txt' for item in manifest['files'])
 actual={p.stem for p in HERE.iterdir() if re.fullmatch(PREFIX+r'-(?:calculation|direct|public)-\d+\.json',p.name)}
 assert actual==set(ATTEMPTS),actual
 for stem,code in ATTEMPTS.items():
  meta=json.loads((HERE/(stem+'.json')).read_text())
  assert meta['exit_code']==code,(stem,meta['exit_code'])
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert '-Dlinter.all=true' in meta['command']
  assert Path(meta['command'][-1]).name==meta['source']
  assert digest((HERE/meta['source']).read_bytes())==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
  assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  started=datetime.datetime.fromisoformat(meta['started_at'])
  ended=datetime.datetime.fromisoformat(meta['observed_at'])
  assert 0<=(ended-started).total_seconds()<300
  usage=json.loads((HERE/(stem+'.usage.json')).read_text())
  assert usage['age_seconds']<120 and usage['remaining_percent']>1
 source=(HERE/(PREFIX+'.lean')).read_text()
 assert digest(source.encode())==FINAL
 assert source.encode()==(HERE/(PREFIX+'-direct-1.source.lean')).read_bytes()
 assert not (HERE/(PREFIX+'-direct-1.log')).read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows expression root request fuel before current')==1
 for forbidden in ['SourceCurrentNativeOriginalCapturedMuRows.capture_source','SourceCurrentNativeOriginalObservedTerminals.of_observed','SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins','SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions','SourceCurrentNativeOriginalPublicationTrace.build_trace_writers']:
  assert forbidden not in source,forbidden
 assert 'slot_lookup' not in source
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_initial_captured_node_row :\n',1)[1].split(' := checked_witness',1)[0]
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
 printer=(HERE/(PREFIX+'-public.lean')).read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/(PREFIX+'-public-1.source.lean')).read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/(PREFIX+'-public-1.log')).read_text()
 assert len(log.encode())==2105277
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selected=json.loads((HERE/(PREFIX+'-selection.json')).read_text())
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['attempts']==list(ATTEMPTS) and selected['expected_exit_codes']==ATTEMPTS
 assert selected['strict']==PREFIX+'-direct-1'
 assert selected['groups']==[dict(name=PREFIX+'-public-1',pairs=1,kind='constructed',full_proof=True)]
 assert selected['lean_jobs']==2 and selected['failed_attempts']==0
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 assert selected['source_sha256']==FINAL and selected['printer_sha256']==PRINTER
 assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']
 assert selected['initial_branch_forced'] and selected['nonidentity_unfold_calls']
 assert selected['leaves_occurrence']==1 and selected['encode_slot_claim'] is False
 peaks=(HERE/(PREFIX+'-peaks-final.txt')).read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=2,failed_attempts=0,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
