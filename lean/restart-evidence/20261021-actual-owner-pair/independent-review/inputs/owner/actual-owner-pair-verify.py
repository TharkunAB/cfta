#!/usr/bin/env python3
"""Check the actual same-owner geometry proof and immutable capped receipts."""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE='SourceCurrentActualOwnerPair.lean'
HEAD='MicroCFTA.SourceCurrentActualOwnerPair.required_pair'
def sha(data:bytes)->str:return hashlib.sha256(data).hexdigest()
def check(base:Path,item:dict)->None:
 data=(base/item['path']).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256'],item['path']
def main()->None:
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));p.add_argument('--live',action='store_true');args=p.parse_args()
 manifest=json.loads((HERE/'actual-owner-pair-manifest.json').read_text())
 for item in manifest['files']:check(HERE,item)
 for item in manifest['sources']:
  check(HERE/'inputs/root',item)
  if args.live:check(args.root,item)
 assert json.loads((HERE/'actual-owner-pair-source-pins.json').read_text())['files']==manifest['sources']
 s=json.loads((HERE/'actual-owner-pair-selection.json').read_text());assert s['finalized'] and s['public_heads']==[HEAD]
 assert s['lean_jobs']==3 and s['infrastructure_attempts']==0 and s['strict_jobs']==2 and s['public_jobs']==1
 assert s['failed_checks']==1 and s['warning_checks']==0 and s['new_public_pairs']==1
 assert s['canonical_jobs']==s['constructed_pairs']==0 and not s['unselected_successes']
 source=(HERE/SOURCE).read_text();assert sha(source.encode())==s['source_sha256']
 assert source==(HERE/(s['selected_strict']+'.source.lean')).read_text()
 assert len(source.splitlines())==189
 assert re.findall(r'^theorem (\w+)',source,re.M)==['required_pair']
 assert not re.search(r'^(?:def|inductive|structure|axiom) |\bsorry\b|\badmit\b|native_decide|trustCompiler',source,re.M)
 for term in ['SourceCurrentRequiredPositiveChronology.pass','SourceCurrentPositiveOwnerPair.same_child_pair']:
  assert source.count(term)==1,term
 for term in ['private theorem rel_covers','private theorem prefix_family','SourceCurrentOuterOriginDependencies.combine_covers','SourceCurrentConjunctionEquality.accessor_correct','SourceCurrentAllocatedInheritedPrefix.run_combine','precheckReceipt.classes records rfl','retained.fields','SourceEqualityClassOrder.ordered_perm','rel_covers coveredFamily related']:
  assert term in source,term
 old=(HERE/'actual-owner-pair-prelaunch-1.source.lean').read_text()
 assert sha(old.encode())=='314b3c7190cdc50fbee2b47912b89e3dcd557edf73dba1288b93e3d41fdb47fe'
 renamed=old.replace('(prefix :','(precheckReceipt :').replace('prefix.classes','precheckReceipt.classes')
 assert renamed==(HERE/'actual-owner-pair-direct-1.source.lean').read_text()
 repaired=renamed.replace('Record.paths','SourceEqualityClassOrder.Record.paths').replace('change .ok (some (.contradiction : EqValue)) = .ok (some combined) at actual','change (Except.ok (some (.contradiction : EqValue)) : Except String (Option EqValue)) =\n        Except.ok (some combined) at actual')
 assert repaired==source
 plan_signature=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
 planned_type=plan_signature.split('theorem required_pair',1)[1].split('\nend MicroCFTA.SourceCurrentActualOwnerPair',1)[0]
 actual_type=source.split('theorem required_pair',1)[1].split(' := by',1)[0]
 normalized=planned_type.replace('(prefix :','(precheckReceipt :').replace('Record.paths','SourceEqualityClassOrder.Record.paths')
 assert actual_type==normalized
 assert s['plan_type_comparison']=='exact source type after binder alpha-renaming and projection qualification'
 ledger=json.loads((HERE/'actual-owner-pair-attempt-ledger.json').read_text())
 assert len(ledger['attempts'])==3 and all(x['lean_launched'] for x in ledger['attempts'])
 assert ledger['unexecuted_source_snapshots']==[{'path':'actual-owner-pair-prelaunch-1.source.lean','sha256':sha(old.encode()),'lean_launched':False,'reason':'complete source-review snapshot before reserved-binder alpha-renaming; not a command attempt'}]
 for item in ledger['attempts']:
  stem=item['name'];meta_path=HERE/(stem+'.json');log_path=HERE/(stem+'.log');meta=json.loads(meta_path.read_text())
  assert sha(meta_path.read_bytes())==item['receipt_sha256'] and sha(log_path.read_bytes())==item['log_sha256']
  assert meta['exit_code']==item['exit_code']
  assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G' and meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
  assert '-Dlinter.all=true' in meta['command'] and meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
  assert sha((HERE/meta['source']).read_bytes())==meta['sha256']
  assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  usage=json.loads((HERE/(stem+'.usage.json')).read_text());assert usage['age_seconds']<120 and usage['remaining_percent']>1
 assert not(HERE/(s['selected_strict']+'.log')).read_bytes()
 failed=(HERE/'actual-owner-pair-direct-1.log').read_text()
 assert 'Unknown identifier' in failed and 'Record' in failed and 'Invalid dotted identifier notation' in failed
 printer=(HERE/(s['selected_public']+'.source.lean')).read_text();assert printer.startswith(source)
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printer
 for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+HEAD+'\n')==1
 log=(HERE/(s['selected_public']+'.log')).read_text();assert len(log.encode())==s['public_log_bytes']==409548
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 checked=log.split('@'+HEAD+' : ',1)[1].split('\ntheorem '+HEAD+' : ',1)[0]
 printed=log.split('theorem '+HEAD+' : ',1)[1].split("'"+HEAD+"'",1)[0];typ,body=printed.split(':=',1)
 assert re.sub(r'\s+','',checked)==re.sub(r'\s+','',typ)
 assert typ.strip() and body.strip() and '_private' not in typ
 axioms=re.search("'"+re.escape(HEAD)+r"' depends on axioms:\s*\[([^\]]*)\]",log);assert axioms
 names=set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',axioms.group(1)).strip()));assert names=={'propext','Classical.choice','Quot.sound'},names
 print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),'lean_jobs':3,'infrastructure_attempts':0,'failed_checks':1,'new_public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,'live':args.live,'manifest_sha256':sha((HERE/'actual-owner-pair-manifest.json').read_bytes())},indent=2))
if __name__=='__main__':main()
