import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
HEAD='MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows'
def main():
 parser=argparse.ArgumentParser()
 parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
 parser.add_argument('--live',action='store_true')
 args=parser.parse_args()
 manifest=json.loads((HERE/'captured-node-rows-manifest.json').read_text())
 for base,entries in [(HERE,manifest['files']),(HERE/'inputs',manifest['sources'])]:
  for entry in entries:
   data=(base/entry['path']).read_bytes()
   assert len(data)==entry['bytes'],entry['path']
   assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
 if args.live:
  for entry in manifest['sources']:
   data=(args.root/entry['path']).read_bytes()
   assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
 assert json.loads((HERE/'captured-node-rows-source-pins.json').read_text())['files']==manifest['sources']
 source=(HERE/'SourceCurrentNativeOriginalCapturedNodeRows.lean').read_text()
 assert re.findall(r'^theorem (\w+)',source,re.M)==['capture_node_rows']
 assert source.count('rcases SourceCurrentNativeCapturedMuUnfoldRows.capture')==1
 assert source.count('SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins')==1
 for name in ['header.lean.txt','captured-unfold-node-snippet.lean.txt','generated-branch.lean.txt','public-producer.lean.txt']:
  assert (HERE/name).read_text() in source,name
 assert hashlib.sha256((HERE/'captured-unfold-node-snippet.lean.txt').read_bytes()).hexdigest()=='a05c7a7836312e4f606e88b1c18c6b10fc105090ad29b2a16897ae3ff2fb7ca3'
 lower=(HERE/'inputs/lean/MicroCFTA/SourceCurrentNativeCapturedMuUnfoldRows.lean').read_text()
 cap=lower.index('theorem capture (')
 generated=lower[lower.index('    ∃ prefixFuel suffixFuel',cap):lower.index(' := by\n',cap)]
 assert generated==(HERE/'generated-branch.lean.txt').read_text()
 assert 'exact .inr generated' in source
 for expected in ['SourceCurrentNativePublicationTrace.source_trace original actual initial',
  'InternedStoredSubstitution.leaves_available siteBody current.native.machine.heap',
  'nodeOrigins outerIndex outer selectedOuter storedRow (bodySame ▸ inside)',
  'entry = outer.entry ∧ body = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary',
  'call.output = storedRow ∧ Grows after outer.afterBody']:
  assert expected in source,expected
 assert not re.search(r'_private|\bsorry\b|\badmit\b',source)
 for stem,code in [('captured-node-rows-direct-1',1),('captured-node-rows-direct-2',0),('captured-node-rows-public-1',0)]:
  meta=json.loads((HERE/(stem+'.json')).read_text())
  assert meta['exit_code']==code and '-Dlinter.all=true' in meta['command']
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
  assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  usage=json.loads((HERE/(stem+'.usage.json')).read_text())
  assert usage['remaining_percent']>1 and usage['age_seconds']<120
 assert 'Failed to infer type of binder `storedRows`' in (HERE/'captured-node-rows-direct-1.log').read_text()
 assert 'Ambiguous term' in (HERE/'captured-node-rows-direct-1.log').read_text()
 assert (HERE/'captured-node-rows-direct-2.source.lean').read_text()==source
 assert not (HERE/'captured-node-rows-direct-2.log').read_bytes()
 printer=(HERE/'captured-node-rows-public-1.source.lean').read_text()
 assert printer.startswith(source)
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printer
 for directive in ['#check @','#print ','#print axioms ']:
  assert printer.count(directive+HEAD)==1
 log=(HERE/'captured-node-rows-public-1.log').read_text()
 printed_type=re.search(r'^theorem '+re.escape(HEAD)+r'.*? :=',log,re.M|re.S)
 assert printed_type and '_private' not in printed_type.group() and 'captured_unfold_nodes' not in printed_type.group()
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:
  assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selection=json.loads((HERE/'captured-node-rows-selection.json').read_text())
 assert selection['public_heads']==[HEAD] and manifest['public_heads']==[HEAD]
 assert selection['lean_jobs']==3 and selection['failed_attempts']==1
 print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),
  'lean_jobs':3,'failed_attempts':1,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,'live':args.live}))
if __name__=='__main__':main()
