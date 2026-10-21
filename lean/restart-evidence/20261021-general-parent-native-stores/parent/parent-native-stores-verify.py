#!/usr/bin/env python3
"""Check the all-branch Parent theorem and immutable capped receipts."""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE='SourceCurrentActualParentNativeStores.lean'
HEAD='MicroCFTA.SourceCurrentActualParentNativeStores.parent'
def sha(data:bytes)->str:return hashlib.sha256(data).hexdigest()
def check(base:Path,item:dict)->None:
 r=Path(item['path']);assert not r.is_absolute() and '..' not in r.parts
 data=(base/r).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256'],item['path']
def main()->None:
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));p.add_argument('--live',action='store_true');args=p.parse_args()
 manifest=json.loads((HERE/'parent-native-stores-manifest.json').read_text())
 for item in manifest['files']:check(HERE,item)
 for item in manifest['sources']:
  check(HERE/'inputs/root',item)
  if args.live:check(args.root,item)
 assert json.loads((HERE/'parent-native-stores-source-pins.json').read_text())['files']==manifest['sources']
 s=json.loads((HERE/'parent-native-stores-selection.json').read_text());assert s['finalized'] and s['public_heads']==[HEAD]
 assert s['lean_jobs']==3 and s['infrastructure_attempts']==0 and s['strict_jobs']==2 and s['public_jobs']==1
 assert s['failed_checks']==1 and s['warning_checks']==1 and s['new_public_pairs']==1
 assert s['canonical_jobs']==s['constructed_pairs']==0 and not s['unselected_successes']
 source=(HERE/SOURCE).read_text();assert sha(source.encode())==s['source_sha256']=='f0a01cf4c787c523b29f357b0d6f0917576dce06db0c6daa684b4fee9ed7b75b'
 assert source==(HERE/(s['selected_strict']+'.source.lean')).read_text() and len(source.splitlines())==262
 assert re.findall(r'^theorem (\w+)',source,re.M)==['parent']
 assert not re.search(r'^(?:def|inductive|structure|axiom) |\bsorry\b|\badmit\b|native_decide|trustCompiler',source,re.M)
 for term in ['SourceCurrentActualParentSemanticReads.parent','SourceCurrentRequiredPositiveChronology.pass','SourceCurrentAllocatedMkEdge.finite','SourceEqualityMkEdgeAllocation.build_receipt','SourceCurrentConjunctionClassScanSoundness.verified']:
  assert source.count(term)==1,term
 for term in ['private theorem constructed','private theorem classes','cases numeric.reads','cases reads with','| stopped first =>','| completed first second last =>','| rejected =>','| unchanged =>','| emptyChildren =>','| classes classReads =>','SourceCurrentScanNumeric.complete','SourceCurrentConjunctionRequired.selected_primary','SourceCurrentNativePositiveSupportAdvance.advance','nodeRecords','.retain _ _','finalAdmission','ConstrainedCapOperandFrame.current prefixFrame']:
  assert term in source,term
 old=(HERE/'parent-native-stores-prelaunch.source.lean').read_text();assert sha(old.encode())=='39d513716fe26c16a37cbf100aeaba527251c3fea549ade0a246a93abef12a5e'
 stoppedRepair=old.replace('''      exact ⟨inventory, finalReady, admitted.advance _ extension, effects,
''','''      obtain ⟨next, _ready, finalAdmission, _effects, _originals, _correct, _retained, _sound⟩ :=
        SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan ready admitted available
          proper active correct ranges
      exact ⟨next, finalReady, finalAdmission, effects,
''')
 assert stoppedRepair==(HERE/'parent-native-stores-direct-1.source.lean').read_text()
 repaired=stoppedRepair.replace('variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]\n\nomit [DecidableEq Symbol] [DecidableEq Node] in\nprivate theorem constructed\n','private theorem constructed [DecidableEq (EdgeKey Symbol Guard)]\n')
 repaired=repaired.replace('cases SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length <;> rfl','cases SourceEqualityMkEdgeAllocation.accepted (SourceEqualityAccessorAllocation.constraint loaded.stored loaded.guard) children.length <;> rfl')
 repaired=repaired.replace('private theorem classes\n','variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]\n\nprivate theorem classes\n')
 repaired=repaired.replace('      have scanNormal := SourceCurrentUnionNormalScan.scan','      dsimp only at scanDone\n      have scanNormal := SourceCurrentUnionNormalScan.scan');assert repaired==source
 plan=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text();planned=plan.split('theorem parent\n',1)[1].strip();actual=source.split('theorem parent\n',1)[1].split(' := by\n',1)[0].strip();assert planned==actual
 assert s['plan_type_comparison']=='exact textual public header and unchanged public instance order'
 ledger=json.loads((HERE/'parent-native-stores-attempt-ledger.json').read_text());assert len(ledger['attempts'])==3 and all(x['lean_launched'] for x in ledger['attempts'])
 assert ledger['unexecuted_source_snapshots']==[{'path':'parent-native-stores-prelaunch.source.lean','sha256':sha(old.encode()),'lean_launched':False,'reason':'source-review draft with stopped-Scan admission corrected before any Lean command; not a command attempt'}]
 for item in ledger['attempts']:
  stem=item['name'];meta_path=HERE/(stem+'.json');log_path=HERE/(stem+'.log');meta=json.loads(meta_path.read_text())
  assert sha(meta_path.read_bytes())==item['receipt_sha256'] and sha(log_path.read_bytes())==item['log_sha256'] and meta['exit_code']==item['exit_code']
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G' and meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  assert '-Dlinter.all=true' in meta['command'] and meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
  assert sha((HERE/meta['source']).read_bytes())==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  usage=json.loads((HERE/(stem+'.usage.json')).read_text());assert usage['age_seconds']<120 and usage['remaining_percent']>1
 assert not(HERE/(s['selected_strict']+'.log')).read_bytes()
 failed=(HERE/'parent-native-stores-direct-1.log').read_text();assert 'Tactic `rfl` failed' in failed and 'Tactic `rewrite` failed' in failed and 'warning:' in failed and 'omit' in failed
 printer=(HERE/(s['selected_public']+'.source.lean')).read_text();assert printer.startswith(source)
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printer
 for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+HEAD+'\n')==1
 log=(HERE/(s['selected_public']+'.log')).read_text();assert len(log.encode())==s['public_log_bytes']==8857109
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 checked=log.split('@'+HEAD+' : ',1)[1].split('\ntheorem '+HEAD+' : ',1)[0]
 printed=log.split('theorem '+HEAD+' : ',1)[1].split("'"+HEAD+"'",1)[0];typ,body=printed.split(':=',1)
 assert re.sub(r'\s+','',checked)==re.sub(r'\s+','',typ) and typ.strip() and body.strip() and '_private' not in typ
 axioms=re.search("'"+re.escape(HEAD)+r"' depends on axioms:\s*\[([^\]]*)\]",log);assert axioms
 names=set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',axioms.group(1)).strip()));assert names=={'propext','Classical.choice','Quot.sound'},names
 usage_values=[json.loads((HERE/(x['name']+'.usage.json')).read_text())['remaining_percent'] for x in ledger['attempts']];assert usage_values==[50.0,50.0,50.0]
 print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),'lean_jobs':3,'infrastructure_attempts':0,'failed_checks':1,'warning_checks':1,'new_public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,'public_log_bytes':len(log.encode()),'live':args.live,'manifest_sha256':sha((HERE/'parent-native-stores-manifest.json').read_bytes())},indent=2))
if __name__=='__main__':main()
