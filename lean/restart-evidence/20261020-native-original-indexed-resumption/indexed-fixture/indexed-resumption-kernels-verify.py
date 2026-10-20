import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='indexed-resumption-kernels'
ATTEMPTS={PREFIX+'-direct-1':1,PREFIX+'-direct-2':0,PREFIX+'-public-1':0}
NAME='MicroCFTA.OriginalIndexedResumptionFixture.actual_indexed_binder_resumption'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='d1e37939d0fe8e9b7ae0924665a08341ac7a195cd9e861764c04f9835c832818'
PRINTER='02932156e8189e5faad5dd107fb240657ac4851249c6c16a8c2b0d5b4e168aa4'
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
 assert manifest['sources'][0]['sha256']=='25a3d3a9bc737a7cba638e3ae57b80394e0a761c953b94544e90062f03aaeae3'
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
  if code:assert "unexpected token 'prefix'" in (HERE/meta['log']).read_text()
 source=(HERE/(PREFIX+'.lean')).read_text()
 assert digest(source.encode())==FINAL
 assert source.encode()==(HERE/(PREFIX+'-direct-2.source.lean')).read_bytes()
 assert not (HERE/(PREFIX+'-direct-2.log')).read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions original root sourceHeap source_done')==1
 for forbidden in ['SourceCurrentNativeOriginalPublicationTrace.build_trace_writers','SourceCurrentNativeOriginalObservedResume.of_observed','SourceCurrentNativeOriginalUnionDescent.of_observed','SourceCurrentNativeOriginalBinderResume.resume']:
  assert forbidden not in source,forbidden
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_indexed_binder_resumption :\n',1)[1].split(' := checked_witness',1)[0]
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
 printer=(HERE/(PREFIX+'-public.lean')).read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/(PREFIX+'-public-1.source.lean')).read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/(PREFIX+'-public-1.log')).read_text()
 assert len(log.encode())==3847621
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selected=json.loads((HERE/(PREFIX+'-selection.json')).read_text())
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['attempts']==list(ATTEMPTS) and selected['expected_exit_codes']==ATTEMPTS
 assert selected['strict']==PREFIX+'-direct-2'
 assert selected['groups']==[dict(name=PREFIX+'-public-1',pairs=1,kind='constructed',full_proof=True)]
 assert selected['lean_jobs']==3 and selected['failed_attempts']==1
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 assert selected['source_sha256']==FINAL and selected['printer_sha256']==PRINTER
 assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']
 assert selected['source_forcing_helpers_byte_identical']
 peaks=(HERE/(PREFIX+'-peaks-final.txt')).read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=3,failed_attempts=1,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
