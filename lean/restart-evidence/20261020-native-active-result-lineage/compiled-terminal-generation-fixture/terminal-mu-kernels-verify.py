import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
ATTEMPTS={'terminal-mu-kernels-direct-1':0,'terminal-mu-kernels-public-1':0}
NAME='MicroCFTA.CompiledTerminalMuGenerationFixture.actual_terminal_generation'
OPTIONS=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
FINAL='0f0a1fb6db623a7e1716245829a0beef42d0303c08e28386cf93f272c667aff5'
def check(base,item):
 data=(base/item['path']).read_bytes()
 assert len(data)==item['bytes'],('bytes',item['path'])
 assert hashlib.sha256(data).hexdigest()==item['sha256'],('sha256',item['path'])
def main():
 parser=argparse.ArgumentParser()
 parser.add_argument('--root',type=Path,default=next((p for p in HERE.parents if (p/'lean/MicroCFTA').is_dir()),Path('/home/tritlo/Code/mcfta')))
 parser.add_argument('--live',action='store_true')
 args=parser.parse_args()
 manifest=json.loads((HERE/'terminal-mu-kernels-manifest.json').read_text())
 for item in manifest['files']: check(HERE,item)
 for item in manifest['sources']:
  check(HERE,dict(item,path=item['snapshot']))
  if args.live:check(args.root,item)
 assert manifest['sources']==json.loads((HERE/'terminal-mu-kernels-source-pins.json').read_text())['sources']
 assert {p.stem for p in HERE.iterdir() if re.fullmatch(r'terminal-mu-kernels-(?:direct|public)-\d+\.json',p.name)}==set(ATTEMPTS)
 for stem,code in ATTEMPTS.items():
  meta=json.loads((HERE/(stem+'.json')).read_text())
  assert meta['exit_code']==code
  assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
  assert '-Dlinter.all=true' in meta['command']
  assert Path(meta['command'][-1]).name==meta['source']
  assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
  assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  assert datetime.datetime.fromisoformat(meta['observed_at'])>=datetime.datetime.fromisoformat(meta['started_at'])
  usage=json.loads((HERE/(stem+'.usage.json')).read_text())
  assert usage['age_seconds']<120 and usage['remaining_percent']>1
  if code:assert re.search(r'\berror(?:\([^)]*\))?:',(HERE/meta['log']).read_text())
 source=(HERE/'terminal-mu-kernels.lean').read_text()
 assert hashlib.sha256(source.encode()).hexdigest()==FINAL
 assert source.encode()==(HERE/'terminal-mu-kernels-direct-1.source.lean').read_bytes()
 assert not (HERE/'terminal-mu-kernels-direct-1.log').read_bytes()
 assert not re.search(r'\b(?:sorry|axiom)\b',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert source.count('SourceCurrentNativeTerminalGeneration.execute request plan good history semantic entry.key entry')==1
 assert 'SourceCurrentNativeOriginGeneration' not in source
 private_type=source.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
 public_type=source.split('theorem actual_terminal_generation :\n',1)[1].split(' := checked_witness',1)[0]
 assert private_type==public_type
 assert 'SourceCurrentAllocatedNativePhysicalCompletion.Good before' in public_type
 assert 'SourceCurrentNativeEdgeWriterGrowth.History before' in public_type
 assert 'heap.nodeRecords entry.key = none' in public_type
 assert 'Reference.interned entry.identity ∈ stored.free' in public_type
 assert 'SourceCurrentNativeQueryRowOrigins.Route siteBefore siteBody' in public_type
 assert 'siteBefore.native.nodes.cells terminalHandle = some ⟨terminal,.returned siteBody⟩' in public_type
 assert 'SourceCurrentNativeWriterReadyRetention.Written terminalHandle terminal siteBody siteBefore.native' in public_type
 assert 'terminalHandle ≠ handle' in public_type
 assert '≠ .swap' in public_type and '≠ .reset' in public_type
 assert 'IntersectionFlatMemoKey.input terminal.left.referenceOf' in public_type
 assert 'IntersectionFlatMemoKey.input terminal.right.referenceOf' in public_type
 assert 'SourceCurrentNativeOptionalTerminalOrigin.Origin' not in public_type
 previous=(HERE/'inputs/prior-compiled-mu-kernels.lean').read_text()
 assert hashlib.sha256(previous.encode()).hexdigest()=='5c04290afac1d2339752010a8364db8689b1e22433390999110246b74af27b32'
 def data_prefix(text):return text.split('private instance : DecidableEq FullSyntax.Formula :=',1)[1].split('private theorem checked_witness :',1)[0]
 assert data_prefix(source)==data_prefix(previous)
 printer=(HERE/'terminal-mu-kernels-public.lean').read_text()
 assert printer.startswith(source)
 assert printer.encode()==(HERE/'terminal-mu-kernels-public-1.source.lean').read_bytes()
 for option in OPTIONS:assert 'set_option '+option in printer
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,printer,re.M))==1
 for directive in ['#check @','#print ','#print axioms ']:assert directive+NAME in printer
 log=(HERE/'terminal-mu-kernels-public-1.log').read_text()
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert re.search(r'^theorem '+re.escape(NAME),log,re.M)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)==1
 for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
 selected=json.loads((HERE/'terminal-mu-kernels-selection.json').read_text())
 assert selected['finalized'] and selected['public_heads']==[NAME]
 assert selected['attempts']==list(ATTEMPTS) and selected['strict']=='terminal-mu-kernels-direct-1'
 assert selected['groups']==[dict(name='terminal-mu-kernels-public-1',pairs=1,kind='constructed',full_proof=True)]
 assert selected['lean_jobs']==2 and selected['failed_attempts']==0
 assert selected['production_pairs']==0 and selected['constructed_pairs']==1
 assert selected['canonical'] is None and selected['canonical_jobs']==0
 peaks=(HERE/'terminal-mu-kernels-peaks-final.txt').read_text().splitlines()
 assert len(peaks)==len(ATTEMPTS)
 assert [int(line.split()[-1]) for line in peaks]==list(ATTEMPTS.values())
 assert all(line.split()[2]=='4G' for line in peaks)
 print(json.dumps(dict(status='PASS',pins=len(manifest['files'])+len(manifest['sources']),production_pairs=0,constructed_pairs=1,lean_jobs=2,failed_attempts=0,canonical_jobs=0,mode='live' if args.live else 'ordinary')))
if __name__=='__main__':main()
