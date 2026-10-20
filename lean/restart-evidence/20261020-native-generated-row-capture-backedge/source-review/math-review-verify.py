#!/usr/bin/env python3
"""Verify a source-only independent integration review; run no Lean command."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args();h=Path(__file__).resolve().parent
j=lambda name:json.loads((h/name).read_text())
def digest(path):
 with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(base,item):
 path=base/item['path'];assert path.stat().st_size==item['bytes'] and digest(path)==item['sha256'],item['path']
m=j('math-review-manifest.json')
for item in m['files']:check(h,item)
pins=j('math-review-source-pins.json')['files']
for item in pins:
 check(h/'inputs',item)
 if a.live:check(a.root,item)
s=j('math-review-selection.json');assert (s['owned_lean_runs'],s['owned_public_pairs'],s['owned_constructed_pairs'],s['reused_public_heads'])==(0,0,0,1)
r=h/'reviewed';source=(r/s['source']).read_bytes();assert hashlib.sha256(source).hexdigest()==s['candidate_sha256']
assert source==(r/(s['strict']+'.source.lean')).read_bytes();assert (r/(s['strict']+'.log')).read_bytes()==b''
text=source.decode();assert (h/'authored-core-snippet.lean.txt').read_text().strip() in text
assert text.count('SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows original')==1
assert text.count(':= observed')==1 and text.count('generated_terminal original sourceRoot request fuel')==2
assert 'initialNonempty' not in text and 'entry.key ≠ targetEntry.key' in text
for stem in [s['strict'],s['full']]:
 receipt=json.loads((r/(stem+'.json')).read_text());assert receipt['exit_code']==0
 assert digest(r/receipt['source'])==receipt['sha256']
 assert json.loads((r/receipt['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
 assert receipt['command'][0].endswith('lean4---v4.34.1/bin/lean')
 usage=json.loads((r/(stem+'.usage.json')).read_text());assert usage['remaining_percent']>1 and usage['age_seconds']<120
head='MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge'
forbidden=re.compile(r'failed to pretty print expression|error:|warning:|sorryAx|⋯|…|\.\.\.|maximum recursion|maximum number of heartbeats')
tail='';type_lines=[];in_type=False;type_done=False
with (r/(s['full']+'.log')).open() as f:
 for line in f:
  assert not forbidden.search(line),line[:200]
  tail=(tail+line)[-16384:]
  if not type_done:
   if '@'+head+' :' in line:in_type=True
   if in_type:
    if ':=' in line:
     type_lines.append(line.split(':=',1)[0]);type_done=True
    else:type_lines.append(line)
assert type_done and '_private' not in ''.join(type_lines)
blocks=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",tail,re.S);assert len(blocks)==1
name,axioms=blocks[0];assert name==head
assert set(re.sub(r'\.\{[^}]*\}','',x.strip()) for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
printed=(r/(s['full']+'.source.lean')).read_text()
for opt,value in [('linter.all','true'),('pp.explicit','true'),('pp.fullNames','true'),('pp.proofs','true'),('pp.proofs.threshold','254'),('pp.universes','true'),('pp.deepTerms','true'),('pp.maxSteps','10000000')]:assert f'set_option {opt} {value}' in printed
for command in [f'#check @{head}',f'#print {head}',f'#print axioms {head}']:assert command in printed
assert printed.startswith(text)
assert 'failed to pretty print expression' in (r/'generated-row-backedge-public-1.log').read_text()
installed=False
if a.live and (a.root/s['official_path']).exists():assert (a.root/s['official_path']).read_bytes()==source;installed=True
print(json.dumps(dict(status='PASS',mode='live' if a.live else 'portable',root_pins=len(pins),local_pins=len(m['files']),official_live_checked=installed,owned_lean_runs=0,reused_public_heads=1,full_log_bytes=(r/(s['full']+'.log')).stat().st_size,private_core_authored=True),indent=2))
