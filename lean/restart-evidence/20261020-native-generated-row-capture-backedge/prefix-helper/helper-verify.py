import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
def pin_check(base,entry):
 data=(base/entry['path']).read_bytes()
 assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));parser.add_argument('--live',action='store_true');args=parser.parse_args()
 m=json.loads((HERE/'helper-manifest.json').read_text())
 for entry in m['files']:pin_check(HERE,entry)
 for entry in m['sources']:
  pin_check(HERE/'inputs',entry)
  if args.live:pin_check(args.root,entry)
 for stem,exit_code in m['attempts']:
  meta=json.loads((HERE/(stem+'.json')).read_text())
  assert meta['exit_code']==exit_code
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert '-Dlinter.all=true' in meta['command']
  assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  usage=json.loads((HERE/(stem+'.usage.json')).read_text());assert usage['age_seconds']<120 and usage['remaining_percent']>1
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G' and meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
 assert 'does not depend on any axioms' in (HERE/'normalized-prefix-api-2.log').read_text()
 assert 'sorryAx' not in (HERE/'normalized-prefix-api-2.log').read_text()
 assert 'maximum recursion depth' in (HERE/'normalized-prefix-direct-1.log').read_text()
 assert 'maximum recursion depth' in (HERE/'normalized-prefix-direct-2.log').read_text()
 assert 'maximum recursion depth' in (HERE/'normalized-prefix-direct-3.log').read_text()
 assert 'checkpoint32_yielded' in (HERE/'normalized-prefix-whnf-1.log').read_text()
 assert 'execute.match_1' in (HERE/'normalized-prefix-whnf-2.log').read_text()
 assert 'fail to show termination' in (HERE/'normalized-prefix-whnf-3.log').read_text()
 assert 'native_decide' not in (HERE/'checked-cbv-snippet.lean.txt').read_text()
 assert 'trustCompiler' not in (HERE/'checked-whnf-snippet.lean.txt').read_text()
 print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':8,'failed_attempts':6,'public_pairs':0,'constructed_pairs':0,'canonical_jobs':0,'native_checkpoint_validated':False,'live':args.live}))
if __name__=='__main__':main()
