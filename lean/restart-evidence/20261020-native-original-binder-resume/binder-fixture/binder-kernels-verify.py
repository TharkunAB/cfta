import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ATTEMPTS={'binder-kernels-calculation-1':1,'binder-kernels-calculation-2':0,'binder-kernels-direct-1':1,'binder-kernels-direct-2':1,'binder-kernels-direct-3':0,'binder-kernels-public-1':0}
NAME='MicroCFTA.OriginalBinderFixture.actual_warm_binder'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='3c951a0c3bf7b8200a9a6d3ee273f9bdfaff7c95848bf79644894a4e0361ab99'
PRINTER='91714318d560b6d718ce0ffce0a1ef2df27ed35e41369fcdb71e5bca79a995c8'
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
 manifest=json.loads((HERE/'binder-kernels-manifest.json').read_text())
 for item in manifest['files']:check(HERE,item)
 for item in manifest['sources']:
  check(HERE,dict(item,path=item['snapshot']))
  if args.live:check(args.root,item)
 assert manifest['sources']==json.loads((HERE/'binder-kernels-source-pins.json').read_text())['sources']
 assert not any(item['path']=='binder-kernels-peaks.txt' for item in manifest['files'])
 actual={p.stem for p in HERE.iterdir() if re.fullmatch(r'binder-kernels-(?:calculation|direct|public)-\d+\.json',p.name)}
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
  if code:assert re.search(r'\berror(?:\([^)]*\))?:',(HERE/meta['log']).read_text())
 source=(HERE/'binder-kernels.lean').read_text()
 assert digest(source.encode())==FINAL
 assert source.encode()==(HERE/'binder-kernels-direct-3.source.lean').read_bytes()
 assert not (HERE/'binder-kernels-direct-3.log').read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeOriginalBinderResume.resume original root sourceHeap source_done')==1
 assert source.count('rows⟩ := resumed.2')==1
 assert 'have concrete := rows row first_body_inside' in source
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_warm_binder :\n',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 for token in ['build (.binder false bodySyntax) [] empty = .done first firstHeap','build program [] empty = .done root sourceHeap','firstHeap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary)','event.body = first','Context event.allocated inputs','InternedFreshOrdinarySourceHistory.Reached program [] event.expression inputs event.allocated','buildMany [.var 0] inputs event.allocated','build (.binder false bodySyntax) inputs event.allocated = .done first event.allocated','callback bodySyntax inputs .depth event.allocated','callback bodySyntax inputs (.uninterned (ordinaryLevel depth)) event.allocated','request false depth ordinary (callback bodySyntax inputs) event.allocated','event.allocated.nodes.table (muKey depth ordinary) = some entry','event.allocated.nodeRecords (muKey depth ordinary)','SourceRow (.binder false bodySyntax) inputs event.allocated first event.allocated row','SourceRow event.expression inputs event.allocated raw rawAfter row','row.children = []','Grows event.allocated rawAfter','Grows event.after sourceHeap','SourceCurrentCompletedBuildRootedWriters.Written program [] empty sourceHeap','∃ published : @Publication','Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty published.before)','∃ publishedRaw publishedAfter','(∀ selectedRow, RowAt body selectedRow','RowAt publishedRaw row','published.allocated publishedRaw publishedAfter row']:
  assert token in public_type,token
 assert public_type.index('∃ published : @Publication')<public_type.index('(∀ selectedRow,')
 assert 'SourceCurrentNativeCapturedMuStoredRows.Stored' not in public_type
 assert 'SourceRow.union (index := 1)' in source and '(by cbv) terminal_source' in source
 assert 'Value.mu.inj (first_shape.symm.trans returned)' in source
 printer=(HERE/'binder-kernels-public.lean').read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/'binder-kernels-public-1.source.lean').read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/'binder-kernels-public-1.log').read_text()
 assert len(log.encode())==1025615
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selected=json.loads((HERE/'binder-kernels-selection.json').read_text())
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['attempts']==list(ATTEMPTS) and selected['expected_exit_codes']==ATTEMPTS
 assert selected['strict']=='binder-kernels-direct-3'
 assert selected['groups']==[dict(name='binder-kernels-public-1',pairs=1,kind='constructed',full_proof=True)]
 assert selected['lean_jobs']==6 and selected['failed_attempts']==3
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 assert selected['source_sha256']==FINAL and selected['printer_sha256']==PRINTER
 peaks=(HERE/'binder-kernels-peaks-final.txt').read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=6,failed_attempts=3,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
