import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def check(base,entry):
 path=base/entry['path'];assert path.stat().st_size==entry['bytes'] and digest(path)==entry['sha256'],entry['path']
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));parser.add_argument('--fixture',type=Path,default=Path('/tmp/mcfta-native-generated-row-capture-backedge-fixture'));parser.add_argument('--live',action='store_true');args=parser.parse_args()
 m=json.loads((HERE/'fixture-review-manifest.json').read_text());head=m['public_head']
 for entry in m['files']:check(HERE,entry)
 for base,live,entries in [(HERE/'inputs/root',args.root,m['sources']),(HERE/'inputs/fixture',args.fixture,m['fixture_files'])]:
  for entry in entries:
   check(base,entry)
   if args.live:check(live,entry)
 pins=json.loads((HERE/'fixture-review-source-pins.json').read_text());assert pins['files']==m['sources'] and pins['fixture_files']==m['fixture_files']
 p=HERE/'inputs/fixture';source=(p/'backedge-kernels.lean').read_text()
 assert source.count('SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge')==1
 private_type=source.split('private theorem checked_witness :',1)[1].split(' := by\n',1)[0]
 public_name=head.rsplit('.',1)[1]
 public_type=source.split('theorem '+public_name+' :',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 for text in m['source_checks']:assert text in source,text
 for text in m['public_type_checks']:assert text in public_type,text
 assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
 direct=m['selected']['strict'];public=m['selected']['public']
 selection=json.loads((p/'backedge-kernels-selection.json').read_text());assert selection['finalized'] is True and selection['strict']==direct and selection['selected_public']==public
 assert selection['public_heads']==[head] and selection['groups']==[{'name':public,'pairs':1,'kind':'constructed','full_proof':True}]
 assert digest(p/'backedge-kernels.lean')==selection['source_sha256'] and selection['production_pairs']==0 and selection['constructed_pairs']==1
 for stem in [direct,public]:
  meta=json.loads((p/(stem+'.json')).read_text());assert meta['exit_code']==0 and '-Dlinter.all=true' in meta['command']
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert digest(p/meta['source'])==meta['sha256']
  assert json.loads((p/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G' and meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  usage=json.loads((p/(stem+'.usage.json')).read_text());assert usage['remaining_percent']>1 and usage['age_seconds']<120
 assert (p/(direct+'.source.lean')).read_text()==source
 assert not (p/(direct+'.log')).stat().st_size
 printer=(p/(public+'.source.lean')).read_text();assert printer.startswith(source)
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printer
 for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+head)==1
 bad=re.compile(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.')
 type_seen=False;proof_seen=False
 with (p/(public+'.log')).open() as stream:
  for line in stream:
   assert not bad.search(line),line[:300]
   if line.startswith('theorem '+head):type_seen=True
   if type_seen and line.rstrip().endswith(' :='):proof_seen=True
 assert type_seen and proof_seen
 path=p/(public+'.log')
 with path.open('rb') as stream:
  stream.seek(max(0,path.stat().st_size-2000));tail=stream.read().decode()
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',tail);assert len(reports)==1
 for report in reports:
  assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))=={'propext','Classical.choice','Quot.sound'}
 print(json.dumps({'status':'PASS','pins':sum(len(m[key]) for key in ['files','sources','fixture_files']),'new_lean_jobs':0,'new_proof_pairs':0,'reused_constructed_groups':1,'live':args.live}))
if __name__=='__main__':main()
