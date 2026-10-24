import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-pruning-resume-20261024')
evidence=root/'lean/restart-evidence/20261024-pruning-resume'
assert not evidence.exists()
for name in ['independent-match-review','independent-resume-review','independent-public-review','independent-document-review']:
    assert Path('/tmp/mcfta-pruning-resume-20261024-'+name+'.md').is_file()
evidence.mkdir()
def copy_tree(source,destination,omit_build=False):
    omitted=[]
    for path in sorted(source.rglob('*')):
        if not path.is_file():continue
        relative=path.relative_to(source);data=path.read_bytes()
        if omit_build and (path.suffix in ['.o','.hi'] or data.startswith(b'\x7fELF')):
            omitted.append(dict(path=relative.as_posix(),bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),reason='Native build output; source and logs retained'))
            continue
        target=destination/relative;target.parent.mkdir(parents=True,exist_ok=True)
        if path.name=='baseline-tree.txt':target.with_suffix('.txt.gz').write_bytes(gzip.compress(data,mtime=0))
        else:target.write_bytes(data)
    return omitted
copy_tree(area,evidence/'work')
copy_tree(Path('/tmp/mcfta-pruning-resume-20261024-resume-proposal'),evidence/'resume-proposal')
omitted=copy_tree(Path('/tmp/mcfta-lpo-main-20261024'),evidence/'upstream',True)
(evidence/'upstream/omitted-native-build-outputs.json').write_text(json.dumps(omitted,indent=2)+'\n')
inputs=evidence/'inputs';inputs.mkdir()
for prefix in ['mcfta-pruning-resume-20261024-','mcfta-lpo-main-20261024-']:
    for path in sorted(Path('/tmp').glob(prefix+'*')):
        if path.is_file() and not path.name.startswith('mcfta-pruning-resume-20261024-archive-1.'):
            shutil.copyfile(path,inputs/path.name)
prior=evidence/'previous-publication';prior.mkdir()
for stem in ['archive-1','local-publication-1','authorized-push-1']:
    for suffix in ['json','log','limits.json','usage.json','source.py','peaks.txt']:
        path=Path('/tmp/mcfta-partial-congruence-20261024-'+stem+'.'+suffix)
        assert path.is_file(),path
        shutil.copyfile(path,prior/path.name)
for name in ['seal-result.json','local-publication.json','remote-publication.json','push.log']:
    shutil.copyfile(Path('/tmp/mcfta-partial-congruence-20261024')/name,prior/name)
shutil.copyfile('/tmp/mcfta-partial-congruence-20261024-publication.py',prior/'publication.py')
production=evidence/'production-sources';production.mkdir()
for name in ['SourcePruningPartialMatch','SourcePruningResume']:
    shutil.copyfile(root/'lean/MicroCFTA'/(name+'.lean'),production/(name+'.lean'))
for name in ['pruning-resume','upstream-lpo']:
    shutil.copyfile(root/'lean'/('notes-current-'+name+'.md'),evidence/('notes-current-'+name+'.md'))
shutil.copyfile('/tmp/mcfta-pruning-resume-20261024-verify.py',evidence/'verify-checkpoint.py')
(evidence/'INDEX.md').write_text('''# Ordered pruning resume and LPO integration evidence

The current notes state the exact claims, premises and remaining obligations.
Main PR #169 is merged. Native goldens and focused LPO repair probes passed.
The uncurried comparator reversal remains; its unsafe consumers are repaired.
Two native harness compile failures remain with their exact package fixes.
No local Haskell patch or product test is added.

Work retains six Lean attempts, including the matcher proof-case syntax failure.
The original author draft and exact keyword repairs remain. Both final sources
passed strict checks. Audit passed. Public signatures and axioms were read.
Inputs retain independent reviews, actual commands, fresh allowance and caps.
The preceding checkpoint's post-seal publication receipts are retained.

Run verify-checkpoint.py with --root set to the repository root. It checks the
manifest, every original file, exact upstream replacements and document inverses,
strict source identities, actual raw check reports and public axiom sets.
It does not compile or prove native extraction. Earlier proofs, marked drafts,
repairs, counterexamples and optimized interned code remain. The full goal is
active and incomplete.
''')
files=sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(evidence).as_posix()+'\n' for p in files))
result=subprocess.run(['/usr/bin/python3',str(evidence/'verify-checkpoint.py'),'--root',str(root)],cwd=root,capture_output=True)
report=dict(exit_code=result.returncode,manifest_sha256=hashlib.sha256((evidence/'SHA256SUMS').read_bytes()).hexdigest(),manifest_entries=len(files),stdout=result.stdout.decode(),stderr=result.stderr.decode())
(area/'seal-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));assert result.returncode==0
