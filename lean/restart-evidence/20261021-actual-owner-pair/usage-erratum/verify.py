#!/usr/bin/env python3
"""Check the report-only usage correction without running Lean."""
import argparse,hashlib,json
from pathlib import Path
def sha(b):return hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
m=json.loads((h/'manifest.json').read_text())
for x in m['files']:
 rel=Path(x['path']);assert not rel.is_absolute() and '..' not in rel.parts;b=(h/rel).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
s=json.loads((h/'selection.json').read_text());assert s['finalized'] and s['status']=='REPORT_ERRATUM_ONLY'
assert sha((h/'inputs/actual-owner-pair-review.md').read_bytes())==s['old_report_sha256']=='dd6da171aeb534d00569074ffd51cb4b79979be18fdc2a0901c0febe32b8a4f3'
assert 'Each sample leaves 52 percent usage.' in (h/'inputs/actual-owner-pair-review.md').read_text()
values=[]
for stem in ['actual-owner-pair-direct-1','actual-owner-pair-direct-2','actual-owner-pair-public-1']:
 u=json.loads((h/('inputs/'+stem+'.usage.json')).read_text());assert u['age_seconds']<120 and u['remaining_percent']>1;values.append(u['remaining_percent'])
assert values==s['remaining_percent']==[52.0,52.0,51.0]
for key in ['new_lean_commands','new_lake_commands','new_canonical_commands','new_public_pairs','new_constructed_pairs']:assert s[key]==0
assert s['reused_usage_samples']==3
source=a.root/'lean/MicroCFTA/SourceCurrentActualOwnerPair.lean';matched=False
if a.live and source.exists():assert sha(source.read_bytes())==s['source_sha256'];matched=True
print(json.dumps({'status':'PASS','live':a.live,'optional_root_source_matched':matched,'pins':len(m['files']),'remaining_percent':values,'new_lean_commands':0,'new_public_pairs':0,'manifest_sha256':sha((h/'manifest.json').read_bytes())},indent=2))
