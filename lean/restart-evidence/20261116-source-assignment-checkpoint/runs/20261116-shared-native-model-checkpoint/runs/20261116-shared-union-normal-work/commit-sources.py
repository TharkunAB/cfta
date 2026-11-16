from pathlib import Path
import difflib
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta');work=Path(__file__).parent;base=work.parent
git=lambda *args:subprocess.check_output(['git',*args],cwd=root,text=True).strip()
run=lambda *args:subprocess.run(['git',*args],cwd=root,check=True)
assert git('branch','--show-current')=='formalize'
assert git('rev-parse','HEAD')=='0feb93907f8b8f0f49deb4458fe86c6430e261ee'
assert subprocess.run(['git','diff','--cached','--quiet'],cwd=root).returncode==0
public=base/'20261116-shared-native-model-publication'
report=json.loads((public/'checked.json').read_text())
assert len(report['checks'])==5 and all(c['exit']==0 and not c['nonstandard_axioms'] for c in report['checks'])
for name,digest in json.loads((public/'source-pins.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
old=(work/'BASE-AUDIT.lean.txt').read_text()
assert old==git('show','HEAD:lean/MicroCFTA/Audit.lean')+'\n'
specs=[('SourcePruningEnumerationPreparationUnionNormal','20261116-current-real-selected-preparation-union-normal-union-readback-repair'),
 ('SourcePruningEnumerationSharedDispatchUnionNormal','20261116-current-shared-dispatch-union-normal-explicit-outcome-repair'),
 ('SourcePruningEnumerationSharedCachedTerminalUnionNormal','20261116-current-shared-cached-terminal-union-normal-draft'),
 ('SourcePruningEnumerationSharedChildUnionNormal','20261116-current-shared-child-union-normal-draft')]
desired=''.join('import MicroCFTA.'+name+'\n' for name,_ in specs)+old+'\n'
desired+='\n'.join((base/folder/'PROBES.lean.txt').read_text() for _,folder in specs)
assert desired.count('#print axioms ')==old.count('#print axioms ')+11
(work/'U-ONLY-AUDIT.lean.txt').write_text(desired)
patch=''.join(difflib.unified_diff(old.splitlines(keepends=True),desired.splitlines(keepends=True),
 fromfile='a/lean/MicroCFTA/Audit.lean',tofile='b/lean/MicroCFTA/Audit.lean'))
p=work/'u-only-audit.patch';p.write_text(patch)
run('apply','--cached',str(p))
run('add','-f',*[str(Path('lean/MicroCFTA')/(name+'.lean')) for name,_ in specs])
run('diff','--cached','--check')
run('commit','-q','-m','Prove native preparation and shared continuation normality')
first=git('rev-parse','HEAD')
run('add','-f','lean/MicroCFTA/Audit.lean',
 'lean/MicroCFTA/SourceCurrentAllocatedNativePastGammaEqualEntryPayload.lean',
 'lean/MicroCFTA/EnumerationPendingDomainAssignment.lean')
run('diff','--cached','--check')
run('commit','-q','-m','Derive past entry payloads and current pending assignments')
second=git('rev-parse','HEAD')
result={'native_continuation_code':first,'checked_code':second,'public_gates':5,
 'all_original_sources_preserved':True,'joint_finite_completion_proved':False,'haskell_changed':False}
(work/'SOURCE-COMMITS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
