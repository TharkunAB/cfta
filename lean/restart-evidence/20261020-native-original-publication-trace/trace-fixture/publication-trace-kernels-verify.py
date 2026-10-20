import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='publication-trace-kernels'
ATTEMPTS={PREFIX+'-direct-1':0,PREFIX+'-public-1':0}
NAME='MicroCFTA.OriginalPublicationTraceFixture.actual_strict_publication_order'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='f6d3b7cd18c99580e7930f11099eab4014f6e61725f969f73db896ffe684e7cf'
PRINTER='b18623e71434a2cf847869e098d7ff7990ab57f2f9458d4d7aa753c4ff81794e'
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
 assert manifest['sources'][0]['sha256']=='4269eff77ca39081f7ef89829cee433e4255459acf1b0419f0053dcd3885ddf4'
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
 assert source.count('SourceCurrentNativeOriginalPublicationTrace.build_trace_writers original [] (empty : Heap)')==1
 assert 'SourceCurrentNativeOriginalObservedResume.of_observed' not in source
 assert 'SourceCurrentNativeOriginalUnionDescent.of_observed' not in source
 assert 'SourceCurrentNativeOriginalBinderResume.resume' not in source
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_strict_publication_order :\n',1)[1].split(' := checked_witness',1)[0]
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
  '∃ outerIndex : Nat, ∃ outer, ∃ earlierIndex : Nat, ∃ earlier,',
  'earlierIndex < outerIndex ∧ (events path)[outerIndex]? = some outer',
  '(events path)[earlierIndex]? = some earlier',
  'outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate',
  'muKey firstDepth firstOrdinary = earlier.key',
  'Value.mu firstEntry firstBody firstDepth firstOrdinary = earlier.candidate',
  'outer.afterBody.nodeRecords (muKey firstDepth firstOrdinary) = some first',
  'outer.afterBody.nodeRecords outer.key = none',
  'earlier.afterBody.nodeRecords earlier.key = none',
  'Nonempty (Path outer.allocated outer.afterBody)',
  'Nonempty (Path earlier.allocated earlier.afterBody)',
  'Grows earlier.after outer.afterBody',
  'Extends earlier.after.nodes.issued outer.afterBody.nodes.issued']:
  assert token in public_type,token
 assert public_type.count('∃ path : Path empty sourceHeap,')==1
 assert source.count('obtain ⟨path,sites,finalWriters,precompletion⟩ :=')==1
 assert source.count('finalWriters event.key event.entry event.body event.depth event.ordinary outer_record')==1
 assert source.count('precompletion outerIndex outer outerLookup (muKey firstDepth firstOrdinary)')==1
 for token in ['InternedFreshOrdinaryFacts.callback_verified published.expression published.environment',
               'have bodySame := (Value.mu.inj same).2.1',
               'have present := available.resident firstEntry rfl',
               'have innerHere := earlier_inner_cell outer outerValue',
               'firstEntry firstBody firstDepth firstOrdinary innerFull']:
  assert token in source,token
 previous=(HERE/'inputs/prior-observed-resume-kernels.lean').read_text()
 assert digest(previous.encode())=='ebc3116f7d5680dc6561126e9b9d9510acd1ddcf5ce5761df177d38d3ea09cdd'
 current_helpers=source.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem outer_record :',1)[0].strip()
 previous_helpers=previous.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem source_context :',1)[0].strip()
 assert current_helpers==previous_helpers
 printer=(HERE/(PREFIX+'-public.lean')).read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/(PREFIX+'-public-1.source.lean')).read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/(PREFIX+'-public-1.log')).read_text()
 assert len(log.encode())==1155998
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
 peaks=(HERE/(PREFIX+'-peaks-final.txt')).read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=2,failed_attempts=0,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
