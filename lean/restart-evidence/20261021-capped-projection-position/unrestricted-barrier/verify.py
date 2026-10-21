import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent

def checked(base,e):
 data=(base/e['path']).read_bytes()
 assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']

def main():
 p=argparse.ArgumentParser()
 p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
 p.add_argument('--live',action='store_true')
 a=p.parse_args()
 m=json.loads((HERE/'manifest.json').read_text())
 for e in m['files']:checked(HERE,e)
 for e in m['sources']:
  checked(HERE/'inputs/root',e)
  if a.live:checked(a.root,e)
 assert json.loads((HERE/'source-pins.json').read_text())['files']==m['sources']
 s=json.loads((HERE/'selection.json').read_text())
 assert s['finalized'] and s['classification']=='source-only-semantic-audit-and-unproved-producer-plan'
 assert s['lean_jobs']==s['public_pairs']==s['constructed_pairs']==s['official_edits']==s['new_counterexamples']==0
 assert s['structural_countershape_only']
 text=(HERE/'audit.md').read_text()
 for term in ['PrimaryEndpointCap.endpoint_cap','safe_gate','safe_origin','RecursiveSourcePlain.required','Safe True','same ordered child origins','actual completed projection','not a new checked fixture','does not contain the relevant original false primary gate','original gates']:
  assert term in text,term
 assert not list(HERE.glob('*.lean'))
 cap=(HERE/'inputs/root/lean/MicroCFTA/SourceCurrentPrimaryEndpointCap.lean').read_text()
 assert 'theorem endpoint_cap' in cap and 'theorem reaches_finite' in cap
 safe=(HERE/'inputs/root/lean/MicroCFTA/SourceCurrentClassObservationSpines.lean').read_text()
 definition=safe[safe.index('private inductive Safe'):safe.index('private theorem safe_map')]
 assert '| root' in definition and '| union' not in definition
 source=(HERE/'inputs/root/lean/MicroCFTA/SourceCurrentRecursiveSourcePlain.lean').read_text()
 assert 'theorem required' in source and '(related : Origin original prepared)' in source
 print(json.dumps({'status':'PASS','local_pins':len(m['files']),'root_pins':len(m['sources']),'lean_jobs':0,'new_public_pairs':0,'constructed_pairs':0,'new_counterexamples':0,'live':a.live}))
if __name__=='__main__':main()
