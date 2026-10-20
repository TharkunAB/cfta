import argparse, datetime, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='backedge-kernels'
NAME='MicroCFTA.GeneratedRowCaptureBackedgeFixture.actual_generated_initial_capture_backedge'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
def digest(data): return hashlib.sha256(data).hexdigest()
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
 selected=json.loads((HERE/(PREFIX+'-selection.json')).read_text())
 for item in manifest['files']: check(HERE,item)
 for item in manifest['sources']:
  check(HERE,dict(item,path=item['snapshot']))
  if args.live: check(args.root,item)
 assert manifest['sources']==json.loads((HERE/(PREFIX+'-source-pins.json')).read_text())['sources']
 assert manifest['sources'][0]['sha256']=='b227f8c769a195a6ef29f6d7114e37d74ee57035be0cbcc3ad3c29f6ea42035f'
 assert not any(item['path']==PREFIX+'-peaks.txt' for item in manifest['files'])
 actual={q.stem for q in HERE.glob(PREFIX+'-*.json') if re.fullmatch(PREFIX+r'-(?:calculation|diagnostic|support|direct|public)-\d+',q.stem)}
 expected=selected['expected_exit_codes']
 assert actual==set(expected),(actual,set(expected))
 started={}
 for stem,code in expected.items():
  meta=json.loads((HERE/(stem+'.json')).read_text())
  assert meta['exit_code']==code,(stem,meta['exit_code'])
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert '-Dlinter.all=true' in meta['command']
  assert Path(meta['command'][-1]).name==meta['source']
  assert digest((HERE/meta['source']).read_bytes())==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
  assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  first=datetime.datetime.fromisoformat(meta['started_at']); last=datetime.datetime.fromisoformat(meta['observed_at'])
  assert 0 <= (last-first).total_seconds() <= 330
  started[stem]=first
  usage=json.loads((HERE/(stem+'.usage.json')).read_text())
  assert usage['age_seconds']<120 and usage['remaining_percent']>1
  if code==-15:
   journal=(HERE/(stem+'.journal.txt')).read_text()
   assert "killed by the OOM killer" in journal and "oom-kill" in journal
   assert not (HERE/meta['log']).read_bytes()
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['source']==PREFIX+'.lean'
 source=(HERE/selected['source']).read_text()
 assert digest(source.encode())==selected['source_sha256']
 strict=selected['selected_strict']; public=selected['selected_public']
 assert expected[strict]==0 and expected[public]==0
 assert not (HERE/(strict+'.log')).read_bytes()
 assert source.encode()==(HERE/(strict+'.source.lean')).read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge expression root request fuel')==1
 assert 'SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows' not in source
 assert 'SourceCurrentNativeOriginalCapturedMuRows.capture_source' not in source
 assert 'slot_lookup' not in source and 'native_decide' not in source and 'elab ' not in source
 private=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_generated_initial_capture_backedge :\n',1)[1].split(' := checked_witness',1)[0]
 assert private==public_type
 for token in [
  'build expression [] empty = .done root heap',
  'SourceCurrentAllocatedNativePhysicalCompletion.Good before',
  'SourceCurrentNativeEdgeWriterGrowth.History before',
  'locate 256 0 control before = 60 ∧ fuel = 60',
  'execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current',
  'generatedInputs[1]? = some (.mu entry stored depth ordinary)',
  'heap.nodeRecords entry.key = some (.mu entry stored depth ordinary)',
  'Reference.interned generatedEntry.identity ∈ generatedBody.free',
  'current.native.machine.heap.nodeRecords generatedEntry.key = none',
  'generatedHeap.nodeRecords generatedEntry.key = some (.mu generatedEntry generatedBody generatedDepth generatedOrdinary)',
  'RowAt generatedBody storedRow',
  '∃ event : @Publication Symbol Guard _,',
  '(∀ storedRow, RowAt generatedBody storedRow',
  'SourceRow (.var 2) terminalInputs terminalBefore terminalRaw terminalAfter storedRow',
  'terminalInputs[2]? = some (.mu entry stored depth ordinary)',
  '(.var 2) terminalInputs crossings ∧ crossings.length = 1',
  'entry.key ≠ generatedEntry.key',
  'RowAt stored storedRow',
  '∃ path : Path empty before.native.machine.heap,',
  'producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer',
  '∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,',
  'call.output = storedRow ∧ Grows after outer.afterBody']:
  assert token in public_type,token
 for token in ['private theorem located_fuel : locate 256 0 control before = fuel := by cbv',
  'private def fuel : Nat := 60', 'set_option Elab.async false',
  'SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before',
  'SourceCurrentNativeRootedMuStoredRows.of_written generatedExpression generatedInputs',
  'SourceCurrentNativeCapturedMuUnfoldRows.observe generatedExpression generatedInputs',
  'rows storedRow generated_row',
  'pool_row poolLookup inside',
  'variable_path path',
  'backedge entry stored depth ordinary rfl',
  'prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1']:
  assert token in source,token
 printer=(HERE/(PREFIX+'-public.lean')).read_text()
 assert printer.startswith(source) and digest(printer.encode())==selected['printer_sha256']
 assert printer.encode()==(HERE/(public+'.source.lean')).read_bytes()
 for option in OPTIONS: assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']: assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']: assert directive+NAME in printer
 log=(HERE/(public+'.log')).read_text()
 assert len(log.encode())==selected['public_log_bytes']
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports: assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 assert selected['groups']==[dict(name=public,pairs=1,kind='constructed',full_proof=True)]
 assert selected['strict']==strict
 assert selected['lean_jobs']==len(expected)
 assert selected['failed_attempts']==sum(code!=0 for code in expected.values())
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 assert selected['distinct_new_source_examples']==1 and selected['attempted_source_variants']==3
 assert selected['initial_capture_branch_forced'] and selected['new_generated_target']
 assert selected['leaves_occurrence']==1 and selected['lexical_slot']==2
 assert selected['encode_slot_claim'] is False
 peaks=(HERE/(PREFIX+'-peaks-final.txt')).read_text().splitlines()
 ordered=sorted(expected,key=lambda stem:started[stem])
 ordinary=[code for stem in ordered if (code:=expected[stem])!=-15]
 assert len(peaks)==len(ordinary),(len(peaks),len(ordinary))
 assert [int(line.split()[-1]) for line in peaks]==ordinary
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=len(expected),failed_attempts=selected['failed_attempts'],canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__': main()
