import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ATTEMPTS={'terminal-kernels-direct-1':1,'terminal-kernels-direct-2':0,'terminal-kernels-public-1':0}
NAME='MicroCFTA.OriginalCapturedTerminalFixture.actual_initial_terminal'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='65157a032cc06f392ea577818ad4857740dea4f3453eff39e83742b7d3c67e94'
PRINTER='c11218764337181bcf8b708f913fb00109e9510d51757ca8b6fdd950ca36a216'
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
 manifest=json.loads((HERE/'terminal-kernels-manifest.json').read_text())
 for item in manifest['files']:check(HERE,item)
 for item in manifest['sources']:
  check(HERE,dict(item,path=item['snapshot']))
  if args.live:check(args.root,item)
 assert manifest['sources']==json.loads((HERE/'terminal-kernels-source-pins.json').read_text())['sources']
 assert not any(p['path'].endswith('peaks.txt') for p in manifest['files'])
 actual=set()
 for p in HERE.iterdir():
  if p.suffix=='.json' and re.fullmatch(r'terminal-kernels-(?:direct|public)-\d+\.json',p.name):actual.add(p.stem)
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
  assert datetime.datetime.fromisoformat(meta['observed_at'])>=datetime.datetime.fromisoformat(meta['started_at'])
  usage=json.loads((HERE/(stem+'.usage.json')).read_text())
  assert usage['age_seconds']<120 and usage['remaining_percent']>1
  if code==1:assert re.search(r'\berror(?:\([^)]*\))?:',(HERE/meta['log']).read_text())
 source=(HERE/'terminal-kernels.lean').read_text()
 assert digest(source.encode())==FINAL
 assert source.encode()==(HERE/'terminal-kernels-direct-2.source.lean').read_bytes()
 assert not (HERE/'terminal-kernels-direct-2.log').read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeOriginalCapturedMuRows.capture_source expression root request fuel before current')==1
 assert 'SourceCurrentNativeCapturedMuUnfoldRows.capture request' not in source
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_initial_terminal :\n',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 for token in ['SourceCurrentAllocatedNativePhysicalCompletion.Good before','SourceCurrentNativeEdgeWriterGrowth.History before','0 < fuel ∧ fuel < 128','(leaves siteBody)[1]? = some (.mu entry stored depth ordinary)','heap.nodeRecords entry.key = some (.mu entry stored depth ordinary)','current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary)','Reference.interned entry.identity ∈ stored.free','unfoldedRun = .done unfolded unfoldedHeap','(InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]? = some unfoldedRow','unfoldedRow.entry.key.symbol = ("rec",.top)','unfoldedRow.children = [.mu entry stored depth ordinary]','storedRow.children = [.reference (.interned entry.identity)]','unfoldedRow ≠ storedRow','∀ value after,','RowAt stored storedRow','∃ lexical first last, Calls lexical storedRow.children first unfoldedRow.children last','event.allocated raw rawAfter storedRow','Reached expression []','Path empty event.before','(outerRow left).children[1]? = some (.mu entry stored depth ordinary)','(outerRow right).children[1]? = some (.mu entry stored depth ordinary)']:
  assert token in public_type,token
 assert public_type.index('∃ event : @Publication') < public_type.index('(∀ value after,')
 assert 'SourceCurrentNativeCapturedMuUnfoldRows.Observed' not in public_type
 assert source.count('SourceCurrentNativePublicationTrace.source_trace expression checked.trace rfl')==1
 assert 'prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1' in source
 assert 'rw [missing] at retained' in source
 previous=(HERE/'inputs/prior-original-kernels.lean').read_text()
 assert digest(previous.encode())=='563d380c1b80af6bc8a04c6683d6e651e8349f5e1f83f61aea97c5ec0f3e21fe'
 def data_prefix(text):return text.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem checked_witness :',1)[0]
 assert data_prefix(source)==data_prefix(previous)
 assert source.count('SourceCurrentNativeOriginalObservedTerminals.of_observed expression empty')==1
 assert source.index('SourceCurrentNativeOriginalObservedTerminals.of_observed expression empty') < source.index('storedRows,everyUnfold⟩ := enriched')
 for token in ['Terminal expression event.expression rawAfter row','Terminal expression event.expression rawAfter original','Terminal expression event.expression rawAfter storedRow']:
  assert token in public_type,token
 assert 'match pair == outerPair with' in source
 assert 'Nat.pow_lt_pow_right' in source
 printer=(HERE/'terminal-kernels-public.lean').read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/'terminal-kernels-public-1.source.lean').read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/'terminal-kernels-public-1.log').read_text()
 assert len(log.encode())==872058
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selected=json.loads((HERE/'terminal-kernels-selection.json').read_text())
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['attempts']==list(ATTEMPTS) and selected['expected_exit_codes']==ATTEMPTS
 assert selected['strict']=='terminal-kernels-direct-2'
 assert selected['groups']==[dict(name='terminal-kernels-public-1',pairs=1,kind='constructed',full_proof=True)]
 assert selected['lean_jobs']==3 and selected['failed_attempts']==1
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 assert selected['source_sha256']==FINAL and selected['printer_sha256']==PRINTER
 peaks=(HERE/'terminal-kernels-peaks-final.txt').read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=3,failed_attempts=1,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
