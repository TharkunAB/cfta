import argparse,hashlib,importlib.util,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def main():
 p=argparse.ArgumentParser();p.add_argument('--live',action='store_true');args=p.parse_args()
 pins=json.loads((HERE/'source-doc-pins.json').read_text())['files']
 for item in pins:
  data=(ROOT/item['path']).read_bytes();assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
 ranges=json.loads((HERE/'source-doc-ranges.json').read_text())['ranges'];assert len(ranges)==12 and len({x['text'] for x in ranges[:7]})==1
 for item in ranges:
  assert hashlib.sha256(item['text'].encode()).hexdigest()==item['sha256']
  assert len(item['text'].splitlines())==item['end_line']-item['start_line']+1
  if args.live:
   lines=(ROOT/item['path']).read_text().splitlines(keepends=True);assert ''.join(lines[item['start_line']-1:item['end_line']])==item['text'],item['path']
 spec=importlib.util.spec_from_file_location('probes',HERE/'head-kernels-probe-tools.py');probes=importlib.util.module_from_spec(spec);spec.loader.exec_module(probes)
 selection=json.loads((HERE/'source-doc-selection.json').read_text())
 for stem,source in selection['strict'].items():
  meta=json.loads((HERE/(stem+'.json')).read_text());assert meta['exit_code']==0 and not (HERE/meta['log']).read_bytes();assert probes.sha(HERE/meta['source'])==probes.sha(ROOT/source);probes.check_limits(stem)
 for stem in selection['canonical']+['full-audit-1']:
  meta=json.loads((HERE/(stem+'.json')).read_text());log=(HERE/meta['log']).read_text();assert meta['exit_code']==0 and 'Build completed successfully' in log
  assert not re.search(r'(^|\n)error:',log)
  for warning in re.findall(r'^warning: (.+)$',log,re.M):assert warning=="MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced."
  probes.check_limits(stem)
 for group in selection['groups']:probes.check_group(group)
 audit=(HERE/'full-audit-1.log').read_text();assert 'Build completed successfully (3473 jobs).' in audit and 'Checked axiom dependencies of 73958 MicroCFTA theorems.' in audit
 print(json.dumps({'status':'PASS','live':args.live,'ranges':len(ranges),'pins':len(pins),'reused_public_pairs':5,'reused_constructed_pairs':1,'new_lean_jobs':0,'new_proof_pairs':0}))
if __name__=='__main__':main()
