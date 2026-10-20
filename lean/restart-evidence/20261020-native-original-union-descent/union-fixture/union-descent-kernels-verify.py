import argparse,datetime,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ATTEMPTS={'union-descent-kernels-direct-1':1,'union-descent-kernels-direct-2':0,'union-descent-kernels-public-1':0}
NAME='MicroCFTA.OriginalUnionDescentFixture.actual_forced_binder'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='04d8619d5ab9db5065c28c1ae38db7abe8fa0fd5713dd2eb8d7cfe470b91140c'
PRINTER='4f6aaf412f3c4374284094c5cc125a7926331b87d8c8ce688be23c41cba9ca35'
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
 manifest=json.loads((HERE/'union-descent-kernels-manifest.json').read_text())
 for item in manifest['files']:check(HERE,item)
 for item in manifest['sources']:
  check(HERE,dict(item,path=item['snapshot']))
  if args.live:check(args.root,item)
 assert manifest['sources']==json.loads((HERE/'union-descent-kernels-source-pins.json').read_text())['sources']
 assert not any(item['path']=='union-descent-kernels-peaks.txt' for item in manifest['files'])
 actual={p.stem for p in HERE.iterdir() if re.fullmatch(r'union-descent-kernels-(?:calculation|direct|public)-\d+\.json',p.name)}
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
 source=(HERE/'union-descent-kernels.lean').read_text()
 assert digest(source.encode())==FINAL
 assert source.encode()==(HERE/'union-descent-kernels-direct-2.source.lean').read_bytes()
 assert not (HERE/'union-descent-kernels-direct-2.log').read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeOriginalUnionDescent.of_observed original root sourceHeap source_done')==1
 assert 'SourceCurrentNativeOriginalBinderResume.resume' not in source
 assert source.count('SourceCurrentNativeCapturedMuUnfoldRows.observe original [] empty sourceHeap')==1
 assert source.count('SourceCurrentCompletedBuildRootedWriters.build_writer original [] empty')==1
 assert source.count('SourceCurrentNativeRootedMuStoredRows.of_written original [] empty sourceHeap')==1
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_forced_binder :\n',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 for token in ['build (.binder false bodySyntax) [] empty = .done first firstHeap','build original [] empty = .done sourceRoot sourceHeap','outerEvent.body = first','Context outerEvent.allocated inputs','InternedFreshOrdinarySourceHistory.Reached original [] outerEvent.expression inputs outerEvent.allocated','buildMany [.var 0] inputs outerEvent.allocated','SourceRow (.binder false bodySyntax) inputs outerEvent.allocated first outerEvent.allocated row','SourceRow outerEvent.expression inputs outerEvent.allocated callbackRaw callbackAfter row','RowAt outerEvent.body row','row.children = []','Grows outerEvent.allocated callbackAfter','Grows outerEvent.after sourceHeap','Nonempty (SourceCurrentNativeMuPublication.History empty sourceHeap)','Available sourceHeap outerEvent.candidate','SourceCurrentCompletedBuildRootedWriters.Written original [] empty sourceHeap outerEvent.key outerEvent.candidate','∃ event : @Publication','(∀ row, RowAt body row','∀ value after,','SourceCurrentLiteralRootParts.Row value row','RowAt raw row','SourceRow event.expression','SyntaxBound terminalExpression event.expression']:
  assert token in public_type,token
 assert public_type.index('∃ event : @Publication')<public_type.index('(∀ row, RowAt body row')<public_type.index('∀ value after,')
 assert public_type.count('∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,')==3
 assert public_type.count('∃ call : RowCall')==2
 assert public_type.count('Stored original [] empty sourceHeap')==3
 assert 'terminalExpression = Syntax.binder false bodySyntax ∧' in public_type
 assert public_type.count('UnionDescent event.expression terminalExpression ∧')==3
 assert 'SourceCurrentNativeOriginalObservedResume.of_observed original' not in source
 assert 'terminalSource,terminalDone,kind,nonunion' in source
 assert 'have outerExpression := fixed_outer_expression selectedEvent observedRaw observedAfter row rooted source filtered bodySame' in source
 assert 'have targetSame := forced_terminal actualRoute nonunion kind' in source
 assert 'have binderFacts := choice.resolve_left' in source
 assert 'targetSame,binderFacts⟩' in source
 assert 'generalize sourceSame : nested = source at path' in source
 assert 'generalize sourceSame : outer = source at path' in source
 assert 'node_filter_not_mu source filtered bodyShape' in source
 assert 'SourceRow.union (index := 1)' in source and '(by cbv) terminal_source' in source
 previous=(HERE/'inputs/prior-observed-resume-kernels.lean').read_text()
 assert digest(previous.encode())=='ebc3116f7d5680dc6561126e9b9d9510acd1ddcf5ce5761df177d38d3ea09cdd'
 current_helpers=source.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem no_node_binder_path',1)[0].strip()
 previous_helpers=previous.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem checked_witness :',1)[0].strip()
 assert current_helpers==previous_helpers
 printer=(HERE/'union-descent-kernels-public.lean').read_text()
 assert printer.startswith(source) and digest(printer.encode())==PRINTER
 assert printer.encode()==(HERE/'union-descent-kernels-public-1.source.lean').read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/'union-descent-kernels-public-1.log').read_text()
 assert len(log.encode())==2445517
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selected=json.loads((HERE/'union-descent-kernels-selection.json').read_text())
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['attempts']==list(ATTEMPTS) and selected['expected_exit_codes']==ATTEMPTS
 assert selected['strict']=='union-descent-kernels-direct-2'
 assert selected['groups']==[dict(name='union-descent-kernels-public-1',pairs=1,kind='constructed',full_proof=True)]
 assert selected['lean_jobs']==3 and selected['failed_attempts']==1
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 assert selected['source_sha256']==FINAL and selected['printer_sha256']==PRINTER
 assert selected['distinct_new_source_examples']==0 and selected['source_data_helpers_byte_identical']
 peaks=(HERE/'union-descent-kernels-peaks-final.txt').read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=3,failed_attempts=1,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
