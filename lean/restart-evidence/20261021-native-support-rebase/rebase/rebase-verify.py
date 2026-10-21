import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
HEAD='MicroCFTA.SourceCurrentNativePositiveSupportRebase.rebase'

def checked(base,e):
 data=(base/e['path']).read_bytes()
 assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']

def main():
 p=argparse.ArgumentParser()
 p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
 p.add_argument('--live',action='store_true')
 a=p.parse_args()
 m=json.loads((HERE/'rebase-manifest.json').read_text())
 for e in m['files']: checked(HERE,e)
 for e in m['sources']:
  checked(HERE/'inputs/root',e)
  if a.live: checked(a.root,e)
 assert json.loads((HERE/'rebase-source-pins.json').read_text())['files']==m['sources']
 native=next(e for e in m['sources'] if e['path'].endswith('/SourceCurrentNativeRequestPositivePositions.lean'))
 assert native['sha256']=='e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727'
 s=json.loads((HERE/'rebase-selection.json').read_text())
 assert s['finalized'] and s['public_heads']==[HEAD]
 assert s['lean_jobs']==2 and s['failed_checks']==s['constructed_pairs']==s['canonical_jobs']==0
 assert s['strict_jobs']==s['public_jobs']==s['new_public_pairs']==1
 source=(HERE/s['source']).read_text()
 assert hashlib.sha256(source.encode()).hexdigest()==s['source_sha256']
 assert source==(HERE/(s['selected_strict']+'.source.lean')).read_text()
 assert len(source.splitlines())==49
 assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
 assert len(re.findall(r'^theorem ',source,re.M))==1
 assert not re.search(r'^(?:def|structure|inductive|private) ',source,re.M)
 for term in ['supported.1.bounded, supported.1.linked','supported.2.bounded, supported.2.linked','origins.nodes handle ⟨request, .returned result⟩ found','origins.edges handle ⟨request, .returned result⟩ found','(origin.inputs_back inputs)','(origin.inputs_back sourceFacts inputs)']:
  assert term in source,term
 assert source.count('SourceCurrentConstrainedCapCheckedJointOrigins.bindings_back')==2
 for name,code in s['attempts'].items():
  meta=json.loads((HERE/(name+'.json')).read_text())
  assert meta['exit_code']==code
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
  assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  usage=json.loads((HERE/(name+'.usage.json')).read_text())
  assert usage['age_seconds']<120 and usage['remaining_percent']>1
  assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
  assert '-Dlinter.all=true' in meta['command']
  assert meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
 assert not (HERE/(s['selected_strict']+'.log')).read_bytes()
 printer=(HERE/(s['selected_public']+'.source.lean')).read_text()
 assert printer.startswith(source)
 assert hashlib.sha256(printer.encode()).hexdigest()==s['public_printer_sha256']
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printer
 for directive in ['#check @','#print ','#print axioms ']:
  assert printer.count(directive+HEAD+'\n')==1
 log=(HERE/(s['selected_public']+'.log')).read_text()
 assert len(log.encode())==s['public_log_bytes']
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 axioms=re.search(r"'"+re.escape(HEAD)+r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
 assert axioms
 names=set() if axioms.group(1) is None else set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',axioms.group(1)).strip()))
 assert names <= {'propext','Classical.choice','Quot.sound'},names
 body=log.split('theorem '+HEAD,1)[1].split("'"+HEAD+"'",1)[0]
 typ,proof=body.split(':=',1)
 assert typ.strip() and proof.strip() and '_private' not in typ
 assert hashlib.sha256((HERE/'inputs/plan/plan.md').read_bytes()).hexdigest()=='bc19179b08b247076776512d5b5ff4e182e60010311571c04b224763e3dbca73'
 print(json.dumps({'status':'PASS','local_pins':len(m['files']),'root_pins':len(m['sources']),'lean_jobs':2,'failed_checks':0,'new_public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,'full_log_bytes':s['public_log_bytes'],'live':a.live}))
if __name__=='__main__':main()
