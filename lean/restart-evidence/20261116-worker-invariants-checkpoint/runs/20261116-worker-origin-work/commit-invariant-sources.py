from pathlib import Path
import difflib
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta');work=Path(__file__).parent;base=work.parent
git=lambda *args:subprocess.check_output(['git',*args],cwd=root)
run=lambda *args:subprocess.run(['git',*args],cwd=root,check=True)
assert git('branch','--show-current').strip()==b'formalize'
assert git('rev-parse','HEAD').strip()==b'5e49f6ab2549d267822c37081ce7878973344a5f'
assert subprocess.run(['git','diff','--cached','--quiet'],cwd=root).returncode==0
public=base/'20261116-worker-invariants-publication'
report=json.loads((public/'checked.json').read_text())
assert len(report['checks'])==5 and all(c['exit']==0 and not c['nonstandard_axioms'] for c in report['checks'])
for name,digest in json.loads((public/'source-pins.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
old=(work/'PRE-CALLBACK-AUDIT.lean.txt').read_bytes();assert old==git('show','HEAD:lean/MicroCFTA/Audit.lean')
groups=[('Preserve callback values and actual prefix buckets', [('SourcePruningEnumerationRecordTypesValues', '20261116-current-record-types-values-core-binders-repair', 'PROBES.lean.txt'), ('SourcePruningEnumerationPreparationNoneBuckets', '20261116-current-real-preparation-none-buckets-draft', 'PROBES.lean.txt'), ('SourcePruningEnumerationRealPrefixNoneBuckets', '20261116-current-real-prefix-none-unit-match-repair', 'PROBES.lean.txt')]), ('Prove full eager-worker union normality at original budgets', [('SourcePruningEnumerationSharedEagerUnionNormalWhole', '20261116-current-real-worker-union-normal-whole-success-reduction-repair', 'PROBES.lean.txt')]), ('Derive full source operands from actual domain entries', [('SourceCurrentAllocatedNativeSourceEmptyEnterOperands', '20261116-current-stored-dispatch-empty-enter-operands-case-transport-repair', 'PROBES.lean.txt'), ('SourceCurrentAllocatedNativeSourceEnterFullOperands', '20261116-current-source-old-new-enter-full-operands-draft', 'PROBES.lean.txt')])]
cumulative=[];commits=[]
for number,(title,specs) in enumerate(groups,1):
    cumulative+=specs
    if number<3:
        desired=''.join('import MicroCFTA.'+name+'\n' for name,_,_ in cumulative).encode()+old+b'\n'
        desired+=b'\n'.join((base/folder/probe).read_bytes() for _,folder,probe in cumulative)
        (work/f'INVARIANT-AUDIT-GROUP-{number}.lean.txt').write_bytes(desired)
        previous=git('show',':lean/MicroCFTA/Audit.lean')
        patch=''.join(difflib.unified_diff(previous.decode().splitlines(keepends=True),desired.decode().splitlines(keepends=True),
            fromfile='a/lean/MicroCFTA/Audit.lean',tofile='b/lean/MicroCFTA/Audit.lean'))
        p=work/f'invariant-audit-group-{number}.patch';p.write_text(patch);run('apply','--cached',str(p))
    else:run('add','--','lean/MicroCFTA/Audit.lean')
    run('add','-f',*[str(Path('lean/MicroCFTA')/(name+'.lean')) for name,_,_ in specs])
    run('diff','--cached','--check');run('commit','-q','-m',title)
    commits.append({'title':title,'commit':git('rev-parse','HEAD').decode().strip()})
result={'source_commits':commits,'checked_code':commits[-1]['commit'],'public_gates':5,
    'new_modules':6,'new_public_theorems':11,'original_sources_preserved':True,
    'full_worker_U_proved':True,'full_worker_None_proved':False,'joint_finite_completion_proved':False,'haskell_changed':False}
(work/'INVARIANT-SOURCE-COMMITS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
