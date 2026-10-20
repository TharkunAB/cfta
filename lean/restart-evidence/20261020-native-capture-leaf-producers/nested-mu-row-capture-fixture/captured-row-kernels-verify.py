import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ATTEMPTS={'captured-row-kernels-direct-1':0,'captured-row-kernels-public-1':0}
NAME='MicroCFTA.NestedCapturedMuRowFixture.actual_nested_row_capture'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='8807b07779bc396921b3d13e235be8c97d3705bc2f9a197172c428b57735e29c'
PRINTER='7042a1fc3975dab93c19e8bf52bac28e0bae36678b2ad1c4d2869d949666612d'
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
 manifest=json.loads((HERE/'captured-row-kernels-manifest.json').read_text())
 for item in manifest['files']:check(HERE,item)
 for item in manifest['sources']:
  check(HERE,dict(item,path=item['snapshot']))
  if args.live:check(args.root,item)
 assert manifest['sources']==json.loads((HERE/'captured-row-kernels-source-pins.json').read_text())['sources']
 assert not any(p['path'].endswith('peaks.txt') for p in manifest['files'])
 actual=set()
 for p in HERE.iterdir():
  if p.suffix=='.json' and re.fullmatch(r'captured-row-kernels-(?:direct|public)-\d+\.json',p.name):actual.add(p.stem)
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
 source=(HERE/'captured-row-kernels.lean').read_text()
 assert digest(source.encode())==FINAL
 assert source.encode()==(HERE/'captured-row-kernels-direct-1.source.lean').read_bytes()
 assert not (HERE/'captured-row-kernels-direct-1.log').read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeCapturedMuRowProduction.capture request fuel before current outerPair siteBody siteNext')==1
 assert 'SourceCurrentNativeTerminalGeneration.execute' not in source
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_nested_row_capture :\n',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 for token in ['SourceCurrentAllocatedNativePhysicalCompletion.Good before','SourceCurrentNativeEdgeWriterGrowth.History before','0 < fuel ∧ fuel < 128','(leaves siteBody)[1]? = some (.mu entry stored depth ordinary)','heap.nodeRecords entry.key = none','current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary)','Reference.interned entry.identity ∈ stored.free','prefixFuel < fuel','Written (.binder true (encode (leaves parent)','SourceCurrentNativeQueryRowOrigins.Route siteBefore parent','siteBefore.native.nodes.cells terminalHandle = some ⟨terminal,.returned parent⟩','SourceCurrentNativeWriterReadyRetention.Written terminalHandle terminal parent siteBefore.native','terminalHandle ≠ handle','≠ .swap','≠ .reset','IntersectionFlatMemoKey.input terminal.left.referenceOf','IntersectionFlatMemoKey.input terminal.right.referenceOf']:
  assert token in public_type,token
 assert 'SourceCurrentNativeOptionalTerminalOrigin.Origin' not in public_type
 assert '∀ (rowIndex : Nat) (row : EdgeValue Symbol Guard)' in public_type
 assert '(InternedEdgeResidency.nodeEdges parent)[rowIndex]? = some row' in public_type
 assert 'SourceCurrentNativeActiveRowProduction.Cases siteBefore terminal parent terminalHandle rowIndex row' in public_type
 assert 'SourceCurrentNativeOptionalRowProduction.Origin' not in public_type
 previous=(HERE/'inputs/prior-captured-mu-kernels.lean').read_text()
 assert digest(previous.encode())=='77213d610a4bf32891c3d721c78dc9cfc1946c0b6a111ec61ae45a945cc4b85a'
 def data_prefix(text):return text.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem checked_witness :',1)[0]
 assert data_prefix(source)==data_prefix(previous)
 assert 'SourceCurrentNativeCapturedMuOrigins.capture' not in source
 assert 'match pair == outerPair with' in source
 assert 'Nat.pow_lt_pow_right' in source
 printer=(HERE/'captured-row-kernels-public.lean').read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/'captured-row-kernels-public-1.source.lean').read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/'captured-row-kernels-public-1.log').read_text()
 assert len(log.encode())==961960
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selected=json.loads((HERE/'captured-row-kernels-selection.json').read_text())
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['attempts']==list(ATTEMPTS) and selected['expected_exit_codes']==ATTEMPTS
 assert selected['strict']=='captured-row-kernels-direct-1'
 assert selected['groups']==[dict(name='captured-row-kernels-public-1',pairs=1,kind='constructed',full_proof=True)]
 assert selected['lean_jobs']==2 and selected['failed_attempts']==0
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 assert selected['source_sha256']==FINAL and selected['printer_sha256']==PRINTER
 peaks=(HERE/'captured-row-kernels-peaks-final.txt').read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=2,failed_attempts=0,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
