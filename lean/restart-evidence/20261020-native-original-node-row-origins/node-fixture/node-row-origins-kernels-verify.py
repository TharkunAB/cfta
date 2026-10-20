import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='node-row-origins-kernels'
ATTEMPTS={PREFIX+'-direct-1':0,PREFIX+'-public-1':0}
NAME='MicroCFTA.OriginalNodeRowOriginsFixture.actual_strict_node_row_origin'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='9fcedfe8f4af9c2ed8641d933810e4b02878abedd0195bc8f597b1dc1e68e89c'
PRINTER='898fa1551a67bade1bb2eec2ce3d0c373bd652633ec7964d1fb5fb44634e805b'
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
 assert manifest['sources'][0]['sha256']=='77ebcd45a4f36f0118f175194ccf102bf9af2fb85173e80744a2e48dbeb6371d'
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
 assert source.count('SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins original root sourceHeap source_done')==1
 for forbidden in ['SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions','SourceCurrentNativeOriginalPublicationTrace.build_trace_writers','SourceCurrentNativeOriginalObservedResume.of_observed','SourceCurrentNativeOriginalUnionDescent.of_observed','SourceCurrentNativeOriginalBinderResume.resume']:
  assert forbidden not in source,forbidden
 assert source.count('SourceCurrentPublicationBodySourceRows.publication_body_origin selectedEvent original [] rooted row selectedInside')==1
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_strict_node_row_origin :\n',1)[1].split(' := checked_witness',1)[0]
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
 printer=(HERE/(PREFIX+'-public.lean')).read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/(PREFIX+'-public-1.source.lean')).read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/(PREFIX+'-public-1.log')).read_text()
 assert len(log.encode())==1468808
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
 assert selected['source_forcing_helpers_byte_identical']
 peaks=(HERE/(PREFIX+'-peaks-final.txt')).read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=2,failed_attempts=0,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
