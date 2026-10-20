#!/usr/bin/env python3
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
j=lambda n:json.loads((h/n).read_text())
def checkpin(base,item):
 b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
manifest=j('order-manifest.json')
for item in manifest['files']:checkpin(h,item)
for item in j('order-source-pins.json')['files']:
 checkpin(h/'inputs',item)
 if a.live:checkpin(a.root,item)
s=j('order-selection.json');assert (s['official_public_pairs'],s['constructed_pairs'],s['canonical_runs'],s['auxiliary_readbacks'],s['actual_lean_jobs'],s['retained_failures'])==(0,0,0,3,4,2)
for stem in s['attempts']:
 r=j(stem+'.json');assert r['exit_code']==(1 if stem in s['attempts'][:2] else 0),stem
 b=(h/r['source']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256']
 assert 'leanprover--lean4---v4.34.1/bin/lean' in r['command'][0]
 assert r['wrapper'][1:5]==['--mem','4G','--time','5m']
 assert j(r['limits'])=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 u=j(stem+'.usage.json');assert u['age_seconds']<120 and u['remaining_percent']>1
assert (h/'order-direct-3.log').read_bytes()==b''
assert (h/'SourceCurrentNativePublicationOrderHelpers.lean').read_bytes()==(h/'order-direct-3.source.lean').read_bytes()
t=(h/'order-public-1.log').read_text();assert not re.search(r'error:|warning:|sorryAx|⋯|…|\.\.\.|maximum recursion|maximum number of heartbeats',t)
blocks=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",t,re.S);assert len(blocks)==3
for (_,axioms),head in zip(blocks,s['heads']):
 assert head in _
 names=[re.sub(r'\.\{[^}]*\}','',x.strip()) for x in axioms.split(',') if x.strip()]
 assert set(names)<={'propext','Classical.choice','Quot.sound'},names
source=(h/'order-public-1.source.lean').read_text()
for option,value in [('linter.all','true'),('pp.explicit','true'),('pp.fullNames','true'),('pp.proofs','true'),('pp.proofs.threshold','254'),('pp.universes','true'),('pp.deepTerms','true'),('pp.maxSteps','10000000')]:assert f'set_option {option} {value}' in source
for head in s['heads']:
 for command in [f'#check @{head}',f'#print {head}',f'#print axioms {head}']:assert command in source
assert len((h/'order-peaks-final.txt').read_text().splitlines())==4
print(json.dumps(dict(result='PASS',mode='live' if a.live else 'portable',local_pins=len(manifest['files']),root_pins=len(j('order-source-pins.json')['files']),actual_lean_jobs=4,retained_failures=2,official_public_pairs=0,constructed_pairs=0,auxiliary_readbacks=3),indent=2))
