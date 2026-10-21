#!/usr/bin/env python3
"""Check the source-only completed-sibling resource audit and exact ranges."""
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
s=json.loads((h/'selection.json').read_text());assert s['finalized'] and not s['proof_implemented'] and not s['official_edits'] and s['new_proof_declarations']==s['board_posts']==0
for k in ['new_lean_commands','new_lake_commands','new_canonical_commands','new_public_pairs','new_constructed_pairs']:assert s[k]==pins[k]==0
assert s['existing_unrestricted_sibling_resource_apis'] and s['one_exact_case']=='OuterExecutionAncestry.Step.rows_edge'
for k in ['future_enclosing_return_required','per_sibling_ready_oracle','past_writer_from_current_reader']:assert not s[k]
report=(h/'report.md').read_text()
for term in ['SOURCE-ONLY AUDIT','unproved','OuterInitialActual.node_call','conditional Merge depth storage','not a reflexive heap interval','No future descendants or enclosing rows return','public APIs already return Frame','causal History','Do not keep the old Fits profile unchanged','does not by itself prove native positive Support','No past writer facts are inferred from a later reader']:
 assert term in report,term
assert not list(h.glob('*.lean'))
print(json.dumps({'status':'PASS','live':a.live,'pins':len(m['files'])+len(m['sources']),'root_sources':len(pins['sources']),'reviewed_ranges':len(ranges),'new_lean_commands':0,'new_canonical_commands':0,'new_public_pairs':0,'proof_implemented':False,'manifest_sha256':sha((h/'manifest.json').read_bytes())},indent=2))
