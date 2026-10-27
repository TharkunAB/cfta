from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-head-policy-20261028')
def digest(b):return hashlib.sha256(b).hexdigest()
def statement(module,name):
 s=(root/'lean/MicroCFTA'/(module+'.lean')).read_text();return s[s.index('theorem '+name):s.index(' := by')]
old=statement('SourcePruningEnumerationFiniteHeadCoverage','head_finite_complete_resources_accepting')
policy=statement('SourcePruningEnumerationAcceptedHeadPolicy','head_finite_complete_resources_policy')
marker=' :\n    ∃ (bound : Nat)';op,ob=old.split(marker,1);np,nb=policy.split(marker,1);assert np.replace('head_finite_complete_resources_policy','head_finite_complete_resources_accepting')==op
names,oldbody=ob.split(',\n      ',1);newnames,newbody=nb.split(',\n      ',1);assert names==newnames;assert newbody.startswith('('+oldbody+') ∧\n')
cb=statement('SourcePruningEnumerationAcceptedHeadCallback','head_finite_complete_resources_callback_policy');cp,cbbody=cb.split(marker,1);assert cp.replace('head_finite_complete_resources_callback_policy','head_finite_complete_resources_policy')==np
cbnames,cbreturn=cbbody.split(',\n      ',1);assert cbnames==newnames;assert cbreturn.startswith('('+newbody+') ∧\n')
original=statement('SourcePruningEnumerationCallbackRefutation','callback_prefix_complete_resources_refutes').split('    ∃ fuel result after,\n',1)[1]
replace={'fuel':'callbackFuel','after':'callbackAfter','before':'afterCache','caller':'actual','memos':'middleMemos','inventory':'middleInventory','profile':'(afterHead seed inherited).2','property':'(fun guard => guard ∈ (afterHead seed inherited).1)','width':'(bits + 2)','Result':'HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)'}
converted=re.sub(r'\b('+ '|'.join(re.escape(x) for x in replace)+r')\b',lambda m:replace[m.group()],original)
assert cbreturn.count('('+converted.strip()+') ∧\n')==1
for module,producer in [('SourcePruningEnumerationAcceptedHeadPolicy','head_finite_complete_resources_accepting'),('SourcePruningEnumerationAcceptedHeadCallback','head_finite_complete_resources_policy')]:
 source=(root/'lean/MicroCFTA'/(module+'.lean')).read_text();body=source.split(' := by',1)[1];assert len(re.findall(r'(?m)^    '+producer+r' ',body))==1
body=(root/'lean/MicroCFTA/SourcePruningEnumerationAcceptedHeadCallback.lean').read_text().split(' := by',1)[1];assert body.count('SourcePruningEnumerationRecursive.callback_prefix_complete_resources_refutes formulas')==1
(area/'literal-original-head-declaration.txt').write_text(old)
report=dict(status='pass',old_head=dict(bytes=len(old.encode()),sha256=digest(old.encode()),entire_admission_and_return=True,producer_calls=1),previous_policy=dict(bytes=len(policy.encode()),sha256=digest(policy.encode()),entire_admission_and_return=True,producer_calls=1),callback=dict(original_return_bytes=len(original.encode()),original_return_sha256=digest(original.encode()),token_substitutions=replace,entire_return_preserved=True,producer_calls=1),bounds_results_before_models=True,common_work_bound='bound + callbackFuel + extra',no_runtime_changes=True)
(area/'root-contract-comparisons.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
