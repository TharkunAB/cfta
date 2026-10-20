#!/usr/bin/env python3
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
j=lambda n:json.loads((h/n).read_text())
def checkpin(base,item):
 b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
m=j('math-review-manifest.json')
for item in m['files']:checkpin(h,item)
for item in j('math-review-source-pins.json')['files']:
 checkpin(h/'inputs',item)
 if a.live:checkpin(a.root,item)
s=j('math-review-selection.json');assert (s['owned_lean_runs'],s['owned_public_pairs'],s['owned_constructed_pairs'],s['reused_public_heads'])==(0,0,0,2)
r=h/'reviewed';source=(r/'SourceCurrentNativeOriginalPublicationTrace.lean').read_bytes();assert hashlib.sha256(source).hexdigest()==s['candidate_sha256'];assert source==(r/(s['strict']+'.source.lean')).read_bytes();assert (r/(s['strict']+'.log')).read_bytes()==b''
for stem in [s['strict'],s['full']]:
 receipt=json.loads((r/(stem+'.json')).read_text());assert receipt['exit_code']==0
 b=(r/receipt['source']).read_bytes();assert hashlib.sha256(b).hexdigest()==receipt['sha256'];assert json.loads((r/receipt['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m'];assert 'leanprover--lean4---v4.34.1/bin/lean' in receipt['command'][0]
t=(r/(s['full']+'.log')).read_text();assert not re.search(r'error:|warning:|sorryAx|⋯|…|\.\.\.|maximum recursion|maximum number of heartbeats',t)
heads=['events','build_trace_writers'];blocks=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",t,re.S);assert len(blocks)==2
for (name,axioms),head in zip(blocks,heads):
 assert name.endswith('.'+head);assert set(re.sub(r'\.\{[^}]*\}','',x.strip()) for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
printed=(r/(s['full']+'.source.lean')).read_text()
for opt,value in [('linter.all','true'),('pp.explicit','true'),('pp.fullNames','true'),('pp.proofs','true'),('pp.proofs.threshold','254'),('pp.universes','true'),('pp.deepTerms','true'),('pp.maxSteps','10000000')]:assert f'set_option {opt} {value}' in printed
for head in heads:
 for command in [f'#check @MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.{head}',f'#print MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.{head}',f'#print axioms MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.{head}']:assert command in printed
start=t.index('@MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.build_trace_writers :');stop=t.index(':=',start);assert '_private' not in t[start:stop]
print(json.dumps(dict(result='PASS',mode='live' if a.live else 'portable',local_pins=len(m['files']),root_pins=len(j('math-review-source-pins.json')['files']),owned_lean_runs=0,reused_public_heads=2),indent=2))
