#!/usr/bin/env python3
"""Check the unproved all-branch Parent native-store plan and source ranges."""
from __future__ import annotations
import argparse,hashlib,json
from pathlib import Path
def sha(b:bytes)->str:return hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
m=json.loads((h/'manifest.json').read_text())
for x in m['files']:
 r=Path(x['path']);assert not r.is_absolute() and '..' not in r.parts;b=(h/r).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],str(r)
pins=json.loads((h/'source-pins.json').read_text());assert pins['sources']==m['sources'];ranges=[]
for x in pins['sources']:
 r=Path(x['path']);s=Path(x['snapshot']);assert not r.is_absolute() and '..' not in r.parts and not s.is_absolute() and '..' not in s.parts
 b=(h/s).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];lines=b.splitlines(keepends=True)
 for span in x['reviewed_ranges']:
  start,end=span['start'],span['end'];assert 1<=start<=end<=len(lines);assert sha(b''.join(lines[start-1:end]))==span['sha256'];ranges.append({'path':x['path'],**span})
 if a.live:assert sha((a.root/r).read_bytes())==x['sha256'],str(r)
assert ranges==json.loads((h/'ranges.json').read_text())['ranges']
for x in pins['archived_authority']:
 b=(h/x['snapshot']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
s=json.loads((h/'selection.json').read_text());assert s['finalized'] and s['status']=='SOURCE_ONLY_UNPROVED_PLAN' and not s['proof_implemented'] and not s['official_edits'];assert s['new_proof_declarations']==s['board_posts']==0
for k in ['new_lean_commands','new_lake_commands','new_canonical_commands','new_public_pairs','new_constructed_pairs']:assert s[k]==pins[k]==0
assert s['proposed_public_heads']==['parent'] and s['same_numeric_receipt']
for k in ['caller_scan_ranges','internal_children_equal_result_children','current_reader_implies_historical_writer']:assert not s[k]
plan=(h/'plan.md').read_text();signature=(h/'proposed-signature.lean.txt').read_text()
for term in ['SOURCE-ONLY PLAN','ONCE','stopped Scan','nodeRecords','History.retain','Current','conditional','not a reflexive interval','historical Parent writer','initial','UnionNormal']:
 assert term in plan,term
assert signature.count('theorem parent')==1 and 'PROPOSED TYPE ONLY' in signature and ':= by' not in signature
assert 'parent positive Support' not in signature
for term in ['(normal :','(supported :','(causal :','(merged :','(positiveMemo :','SourceCurrentParentNumeric.Receipt','Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap)']:
 assert term in signature,term
assert not list(h.glob('*.lean'))
print(json.dumps({'status':'PASS','live':a.live,'pins':len(m['files'])+len(m['sources']),'root_sources':len(pins['sources']),'reviewed_ranges':len(ranges),'new_lean_commands':0,'new_lake_commands':0,'new_canonical_commands':0,'new_public_pairs':0,'proof_implemented':False,'manifest_sha256':sha((h/'manifest.json').read_bytes())},indent=2))
