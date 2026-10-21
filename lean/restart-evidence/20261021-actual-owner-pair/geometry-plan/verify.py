#!/usr/bin/env python3
"""Check the source-only owner-geometry plan and exact reviewed source ranges."""
from __future__ import annotations
import argparse,hashlib,json
from pathlib import Path
def sha(data: bytes)->str:return hashlib.sha256(data).hexdigest()
def main()->None:
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();here=Path(__file__).resolve().parent
 manifest=json.loads((here/'manifest.json').read_text())
 for item in manifest['files']:
  rel=Path(item['path']);assert not rel.is_absolute() and '..' not in rel.parts
  data=(here/rel).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256'],str(rel)
 pins=json.loads((here/'source-pins.json').read_text());assert pins['sources']==manifest['sources'];flat=[]
 for item in pins['sources']:
  rel=Path(item['path']);snapshot=Path(item['snapshot']);assert not rel.is_absolute() and '..' not in rel.parts and not snapshot.is_absolute() and '..' not in snapshot.parts
  data=(here/snapshot).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256'],str(rel);lines=data.splitlines(keepends=True)
  for span in item['reviewed_ranges']:
   start,end=span['start'],span['end'];assert 1<=start<=end<=len(lines);assert sha(b''.join(lines[start-1:end]))==span['sha256'];flat.append({'path':item['path'],**span})
  if a.live:assert sha((a.root/rel).read_bytes())==item['sha256'],str(rel)
 assert json.loads((here/'ranges.json').read_text())['ranges']==flat
 s=json.loads((here/'selection.json').read_text());assert s['finalized'] and not s['proposed_result_proved'] and not s['implementation_in_this_package'] and not s['official_edits']
 assert s['proposed_public_heads']==['MicroCFTA.SourceCurrentActualOwnerPair.required_pair']
 for k in ['new_lean_commands','new_lake_commands','new_canonical_commands','new_public_pairs','new_constructed_pairs']:assert s[k]==pins[k]==0
 for k in ['same_selected_row_and_child_slot','whole_class_covers_not_member','live_combined_payload_required','historical_native_stores_remain_genuine','literal_worker_to_admitted_receipts_remains_genuine']:assert s[k]
 for k in ['common_anchor_premise','caller_ancestry_callback','runtime_rank_claim']:assert not s[k]
 plan=(here/'plan.md').read_text();signature=(here/'proposed-signature.lean.txt').read_text()
 for term in ['SOURCE-ONLY PLAN','unproved','SAME row.children','whole-class Covers','historical native Current','does not create them at a historical writer','No reader certificate follows merely from pass.done','not global outer termination']:assert term in plan,term
 assert signature.count('theorem required_pair')==1
 for term in ['(prefix :','(retained :','(required :','(reads :','(current :','(supported :','(causal :','(positiveMemo :','(outerPrefix :','(payload :','EqualityNormalize.Covers','congruenceStep','left ≠ right']:assert term in signature,term
 assert 'back :' not in signature and 'Cap Plain' not in signature
 assert not any(x['path'].endswith('/SourceCurrentNativeRequestPositivePositions.lean') for x in pins['sources'])
 print(json.dumps({'status':'PASS','live':a.live,'root_sources':len(pins['sources']),'reviewed_ranges':len(flat),'pins':len(manifest['files'])+len(manifest['sources']),'new_lean_commands':0,'new_canonical_commands':0,'new_public_pairs':0,'proposed_result_proved':False,'manifest_sha256':sha((here/'manifest.json').read_bytes())},indent=2))
if __name__=='__main__':main()
