import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
HEAD='MicroCFTA.SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions'
def main():
 parser=argparse.ArgumentParser()
 parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
 parser.add_argument('--live',action='store_true')
 args=parser.parse_args()
 manifest=json.loads((HERE/'indexed-resumption-manifest.json').read_text())
 for base,entries in [(HERE,manifest['files']),(HERE/'inputs',manifest['sources'])]:
  for entry in entries:
   data=(base/entry['path']).read_bytes()
   assert len(data)==entry['bytes'],entry['path']
   assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
 if args.live:
  for entry in manifest['sources']:
   data=(args.root/entry['path']).read_bytes()
   assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
 pins=json.loads((HERE/'indexed-resumption-source-pins.json').read_text())
 assert pins['files']==manifest['sources']
 source=(HERE/'SourceCurrentNativeOriginalIndexedResumption.lean').read_text()
 assert re.findall(r'^theorem (\w+)',source,re.M)==['build_row_resumptions']
 assert source.count('SourceCurrentNativeOriginalPublicationTrace.build_trace_writers')==1
 assert not re.search(r'_private|\bsorry\b|\badmit\b',source)
 for name in ['header.lean.txt','joint-helpers.lean.txt','callback-rows.lean.txt','binder-before-snippet.lean.txt','public-producer.lean.txt']:
  assert (HERE/name).read_text() in source,name
 old=(HERE/'inputs/lean/MicroCFTA/SourceCurrentNativeOriginalUnionDescent.lean').read_text()
 joint=old[old.index('variable {Symbol Guard : Type}'):old.index('local notation "Symbol"')]
 assert (HERE/'joint-helpers.lean.txt').read_text()==joint
 snippet=(HERE/'binder-before-snippet.lean.txt').read_bytes()
 assert hashlib.sha256(snippet).hexdigest()=='e93a0b50090f400c4e1ece4dc176079ede1b4fa4c0ad3d7ca197d889916a903f'
 for stem in ['indexed-resumption-direct-1','indexed-resumption-public-1']:
  meta=json.loads((HERE/(stem+'.json')).read_text())
  assert meta['exit_code']==0 and '-Dlinter.all=true' in meta['command']
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
  assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  usage=json.loads((HERE/(stem+'.usage.json')).read_text())
  assert usage['remaining_percent']>1 and usage['age_seconds']<120
 assert (HERE/'indexed-resumption-direct-1.source.lean').read_text()==source
 assert not (HERE/'indexed-resumption-direct-1.log').read_bytes()
 printer=(HERE/'indexed-resumption-public-1.source.lean').read_text()
 assert printer.startswith(source)
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printer
 for directive in ['#check @','#print ','#print axioms ']:
  assert printer.count(directive+HEAD)==1
 log=(HERE/'indexed-resumption-public-1.log').read_text()
 printed_type=re.search(r'^theorem '+re.escape(HEAD)+r'.*? :=',log,re.M|re.S)
 assert printed_type
 for word in ['_private','terminal_resume','terminal_original','callback_rows','binder_before']:
  assert word not in printed_type.group(),word
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:
  assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selection=json.loads((HERE/'indexed-resumption-selection.json').read_text())
 assert selection['public_heads']==[HEAD] and manifest['public_heads']==[HEAD]
 assert selection['lean_jobs']==2 and selection['failed_attempts']==0
 print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),
  'lean_jobs':2,'failed_attempts':0,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,'live':args.live}))
if __name__=='__main__':main()
