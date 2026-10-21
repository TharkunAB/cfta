#!/usr/bin/env python3
"""Check the frozen raw corridor design and exact sources without invoking Lean."""
import argparse,hashlib,json,re
from pathlib import Path

def check(path,entry):
 assert path.is_file() and path.stat().st_size==entry['bytes'],str(path)
 assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'],str(path)

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args()
 h=Path(__file__).resolve().parent;m=json.loads((h/'plan-manifest.json').read_text())
 for e in m['files']:check(h/e['path'],e)
 pins=json.loads((h/'plan-source-pins.json').read_text())['files']
 assert len(pins)==35 and len({e['path'] for e in pins})==35
 for e in pins:
  check(h/'inputs/root'/e['path'],e)
  if a.live:check(a.root/e['path'],e)
 text=(h/'plan.md').read_text()
 for fragment in ['zero Lean jobs','Keep the old 315-line','RawCorridor : List Int -> Node -> Prop',
  'EVERY raw row','All2 Preserves values results','compiled_allowed','build_leaves',
  'HasLeaf','max','SAME class path token','inaccessible private','generic Force','phaseValues',
  'Combining all three into one300-line module is not a credible bound',
  'global renewal rank','unproved']:
  assert fragment in text,fragment
 source=(h/'inputs/root/lean/MicroCFTA/SourceCurrentOriginalGateProjectionCap.lean').read_text()
 assert len(source.splitlines())==315 and 'private inductive Corridor' in source
 edit=(h/'inputs/root/lean/MicroCFTA/SourceCurrentAllocatedSharedEditGraph.lean').read_text()
 assert all(x in edit for x in ['| leaf (actual : Leaf','| recursive (recursive :','| selected (index : Nat)','| unselected (index : Nat)'])
 trace=(h/'inputs/root/lean/MicroCFTA/SourceEqualityClassEdits.lean').read_text()
 assert 'paths.map (fun path => (path.map Int.ofNat, target path))' in trace
 assert not list(h.glob('*.lean')) and not list(h.glob('*-direct-*.json'))
 assert m['scope']=={'lean_jobs':0,'public_pairs':0,'constructed_pairs':0,'status':'UNPROVED_NEXT_PLAN'}
 print(json.dumps({'status':'PASS','live':a.live,'root_pins':len(pins),'local_pins':len(m['files']),'lean_jobs':0,'public_pairs':0,'constructed_pairs':0,'claim':'UNPROVED_NEXT_PLAN'},sort_keys=True))
if __name__=='__main__':main()
