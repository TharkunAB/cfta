#!/usr/bin/env python3
"""Verify the frozen source-only local target plan without invoking Lean."""
import argparse,hashlib,json,re
from pathlib import Path

def check(path,entry):
 assert path.is_file() and path.stat().st_size==entry['bytes'],str(path)
 assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'],str(path)

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True);parser.add_argument('--live',action='store_true');a=parser.parse_args()
 h=Path(__file__).resolve().parent
 manifest=json.loads((h/'plan-manifest.json').read_text())
 for e in manifest['files']:check(h/e['path'],e)
 pins=json.loads((h/'plan-source-pins.json').read_text())['files']
 assert len(pins)==38 and len({e['path'] for e in pins})==38
 for e in pins:
  check(h/'inputs/root'/e['path'],e)
  if a.live:check(a.root/e['path'],e)
 text=(h/'plan.md').read_text()
 for fragment in ['zero Lean jobs','SAME `AllocatedSharedTargetForce.Receipt`','MergeOperand.Receipt.actual',
  'RequiredForestProjectionCap.project','ConstrainedCapMemoMerge.retained','full caps on BOTH exact operands',
  'install','compiled_allowed','SourceEqualityEditCompiledPaths.build_leaves','class_placement',
  'prefix of q','prefix of p','disjoint','phaseValues','No replacement','remain open']:
  assert fragment.lower() in text.lower(),fragment
 assert 'A later class does not capture `prepared` by definitional equality.' in text
 candidate=(h/'inputs/candidate/SourceCurrentRequiredForestProjectionCap.lean').read_text()
 assert len(candidate.splitlines())==88 and re.findall(r'^theorem (\w+)',candidate,re.M)==['project']
 assert 'SourceCurrentOriginalGateProjectionCap.project' in candidate
 assert 'later.available value' in candidate and 'All₂ Origin originals prepared' in candidate
 assert not list(h.glob('*.lean')) and not list(h.glob('*-direct-*.json'))
 assert manifest['scope']=={'lean_jobs':0,'public_pairs':0,'constructed_pairs':0,'status':'UNPROVED_NEXT_PLAN'}
 print(json.dumps({'status':'PASS','live':a.live,'root_pins':len(pins),'local_pins':len(manifest['files']),'lean_jobs':0,'public_pairs':0,'constructed_pairs':0,'claim':'UNPROVED_NEXT_PLAN'},sort_keys=True))
if __name__=='__main__':main()
