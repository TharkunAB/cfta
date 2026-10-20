import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
HEAD='MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge'
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def verify_full(path):
 bad=re.compile(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.')
 in_type=False;type_seen=False;type_done=False
 with path.open() as stream:
  for line in stream:
   assert not bad.search(line),line[:300]
   if line.startswith('theorem '+HEAD):in_type=True;type_seen=True
   if in_type:
    assert '_private' not in line
    if line.rstrip().endswith(' :=') or line.strip()==':=':in_type=False;type_done=True
 assert type_seen and type_done
 with path.open('rb') as stream:
  stream.seek(max(0,path.stat().st_size-1500));tail=stream.read().decode()
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',tail)
 assert len(reports)==1
 for report in reports:
  assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));parser.add_argument('--live',action='store_true');args=parser.parse_args()
 manifest=json.loads((HERE/'generated-row-backedge-manifest.json').read_text())
 for base,entries in [(HERE,manifest['files']),(HERE/'inputs',manifest['sources'])]:
  for entry in entries:
   path=base/entry['path'];assert path.stat().st_size==entry['bytes'] and digest(path)==entry['sha256'],entry['path']
 if args.live:
  for entry in manifest['sources']:
   path=args.root/entry['path'];assert path.stat().st_size==entry['bytes'] and digest(path)==entry['sha256'],entry['path']
 assert json.loads((HERE/'generated-row-backedge-source-pins.json').read_text())['files']==manifest['sources']
 source=(HERE/'SourceCurrentNativeGeneratedRowCaptureBackedge.lean').read_text()
 assert re.findall(r'^theorem (\w+)',source,re.M)==['generated_row_capture_backedge']
 assert source.count(':= observed')==1
 assert source.count('SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows')==1
 assert 'initialNonempty' not in source
 assert (HERE/'generated-backedge-core-snippet.lean.txt').read_text() in source
 assert digest(HERE/'generated-backedge-core-snippet.lean.txt')=='4755ec72d3e077e587ea744c0e404e8a0e5a57b0d7f89089db411b8effbe48c3'
 assert (HERE/'source-done-snippet.lean.txt').read_text() in source
 assert (HERE/'public-producer.lean.txt').read_text() in source
 lower=(HERE/'inputs/lean/MicroCFTA/SourceCurrentNativeOriginalCapturedNodeRows.lean').read_text()
 begin=lower.index('theorem capture_node_rows')
 branch=lower[lower.index('    ∃ prefixFuel suffixFuel',begin):lower.index(' := by\n',begin)]
 assert branch==(HERE/'generated-branch.lean.txt').read_text()
 assert branch in source and 'exact .inr generated' in source
 for fragment in ['source_done terminalSource','slot = crossings.length + originalSlot','captured.free = []',
   'entry.key ≠ targetEntry.key','RowAt body storedRow','call.output = storedRow','call.output = originalRow',
   'capture_same_row original sourceRoot request fuel before current',
   'have resident := capturedAvailable.resident entry rfl','rw [sameKey,targetMissing] at resident',
   'SourceCurrentSourceCaptureOriginalSlots.original_slot path slot',
   'terminalSource,source_done terminalSource,nonunion,terminalContext,terminalReached,bound']:
  assert fragment in source,fragment
 assert not re.search(r'_private|\bsorry\b|\badmit\b',source)
 stems=[('generated-row-backedge-direct-1',1),('generated-row-backedge-direct-2',0),('generated-row-backedge-public-1',0),('generated-row-backedge-public-2',0),('generated-row-backedge-direct-3',0),('generated-row-backedge-public-3',0)]
 for stem,code in stems:
  meta=json.loads((HERE/(stem+'.json')).read_text())
  assert meta['exit_code']==code and '-Dlinter.all=true' in meta['command']
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert digest(HERE/meta['source'])==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
  assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  usage=json.loads((HERE/(stem+'.usage.json')).read_text());assert usage['remaining_percent']>1 and usage['age_seconds']<120
 assert 'Ambiguous term' in (HERE/'generated-row-backedge-direct-1.log').read_text()
 assert 'maybeMu' in (HERE/'generated-row-backedge-direct-1.log').read_text()
 assert not (HERE/'generated-row-backedge-direct-2.log').stat().st_size
 assert not (HERE/'generated-row-backedge-direct-3.log').stat().st_size
 assert (HERE/'generated-row-backedge-direct-3.source.lean').read_text()==source
 with (HERE/'generated-row-backedge-public-1.log').open('rb') as stream:
  stream.seek(-1500,2);assert b'failed to pretty print expression' in stream.read()
 verify_full(HERE/'generated-row-backedge-public-2.log')
 verify_full(HERE/'generated-row-backedge-public-3.log')
 printer=(HERE/'generated-row-backedge-public-3.source.lean').read_text();assert printer.startswith(source)
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printer
 assert 'set_option maxRecDepth 16384' in printer
 for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+HEAD)==1
 selection=json.loads((HERE/'generated-row-backedge-selection.json').read_text())
 assert selection['public_heads']==manifest['public_heads']==[HEAD]
 assert selection['selected_strict']=='generated-row-backedge-direct-3' and selection['selected_public']=='generated-row-backedge-public-3'
 assert selection['lean_jobs']==6 and selection['failed_attempts']==1 and selection['rejected_printers']==1
 print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),'lean_jobs':6,'failed_attempts':1,'rejected_printers':1,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,'live':args.live}))
if __name__=='__main__':main()
