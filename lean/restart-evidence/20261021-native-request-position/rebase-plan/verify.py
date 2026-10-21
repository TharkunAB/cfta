import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent

def check(base,e):
 data=(base/e['path']).read_bytes()
 assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']

def main():
 p=argparse.ArgumentParser()
 p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
 p.add_argument('--live',action='store_true')
 a=p.parse_args()
 m=json.loads((HERE/'manifest.json').read_text())
 for e in m['files']:check(HERE,e)
 for e in m['sources']:
  check(HERE/'inputs/root',e)
  if a.live:check(a.root,e)
 assert json.loads((HERE/'source-pins.json').read_text())['files']==m['sources']
 s=json.loads((HERE/'selection.json').read_text())
 assert s['finalized'] and s['lean_jobs']==s['new_public_pairs']==s['constructed_pairs']==0
 assert s['classification']=='proposed-unproved-source-only-plan'
 data=(HERE/s['api_source']).read_bytes()
 assert hashlib.sha256(data).hexdigest()==s['api_source_sha256']
 source=data.decode()
 assert 'def Support (source : Heap)' in source
 assert 'theorem call (source : Heap)' in source
 assert 'oldStored : OldStore source before.native' in source
 assert 'supported : Support source before.native' in source
 assert 'Support source after.native' in source
 plan=(HERE/'plan.md').read_text()
 for text in ['NodeOrigin.inputs_back','EdgeOrigin.inputs_back','CheckedJointOrigins.bindings_back','FlatMemoThunk.Valid.map','OuterInitialPrefix.reached','Trace.origins','does not return captured origins']:
  assert text in plan,text
 assert not list(HERE.glob('*.source.lean'))
 print(json.dumps({'status':'PASS','local_pins':len(m['files']),'root_pins':len(m['sources']),'lean_jobs':0,'new_public_pairs':0,'constructed_pairs':0,'live':a.live}))
if __name__=='__main__':main()
