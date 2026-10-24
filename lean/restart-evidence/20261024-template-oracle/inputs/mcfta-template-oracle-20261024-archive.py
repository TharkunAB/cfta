import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-template-oracle-20261024')
evidence=root/'lean/restart-evidence/20261024-template-oracle'
assert not evidence.exists()
for name in ['source-review','independent-templates-review','independent-oracle-review','independent-public-review','independent-document-review']:
    assert Path('/tmp/mcfta-template-oracle-20261024-'+name+'.md').is_file()
evidence.mkdir()
def copy_tree(source,destination):
    for path in sorted(source.rglob('*')):
        if not path.is_file():continue
        relative=path.relative_to(source);data=path.read_bytes()
        target=destination/relative;target.parent.mkdir(parents=True,exist_ok=True)
        if path.name=='baseline-tree.txt':target.with_suffix('.txt.gz').write_bytes(gzip.compress(data,mtime=0))
        else:target.write_bytes(data)
copy_tree(area,evidence/'work')
for name in ['templates','oracle']:
    copy_tree(Path('/tmp/mcfta-template-oracle-20261024-'+name+'-proposal'),evidence/(name+'-proposal'))
inputs=evidence/'inputs';inputs.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-template-oracle-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-template-oracle-20261024-archive-1.'):
        shutil.copyfile(path,inputs/path.name)
prior=evidence/'previous-publication';prior.mkdir()
for stem in ['archive-1','local-publication-1','authorized-push-1']:
    for suffix in ['json','log','limits.json','usage.json','source.py','peaks.txt']:
        path=Path('/tmp/mcfta-pruning-resume-20261024-'+stem+'.'+suffix)
        assert path.is_file(),path
        shutil.copyfile(path,prior/path.name)
for name in ['seal-result.json','local-publication.json','remote-publication.json','push.log','publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-resume-20261024')/name,prior/name)
shutil.copyfile('/tmp/mcfta-pruning-resume-20261024-publication.py',prior/'publication.py')
production=evidence/'production-sources';production.mkdir()
for name in ['SourcePruningTemplates','SourcePruningOracle']:
    shutil.copyfile(root/'lean/MicroCFTA'/(name+'.lean'),production/(name+'.lean'))
shutil.copyfile(root/'lean/notes-current-template-oracle.md',evidence/'current-note.md')
shutil.copyfile('/tmp/mcfta-template-oracle-20261024-verify.py',evidence/'verify-checkpoint.py')
(evidence/'INDEX.md').write_text('''# Concrete template oracle observation evidence

The current note states the exact claims, premises and remaining obligations.
Both source modules use full labels and retain symbol refinements. Position-tagged
candidate maps preserve source order and duplicate template values. The callback
keeps every native branch and ordered state read before pure match combination.
Its guarantees concern observations. They do not prove semantic pruning safety.

Work retains all seven Lean attempts, including both strict-check failures.
Owner packages retain preliminary String drafts, the full-label corrections,
source cuts, self-reviews and exact selected-source pins. Inputs retain independent
source, repair, public and document reviews, actual commands, allowance and caps.
Production sources are the exact final strict inputs. Public axiom reports include
standard Classical.choice explicitly. No project axiom or option override is added.
Previous-publication retains the prior checkpoint's post-seal receipts and payload.

Run verify-checkpoint.py with --root set to the repository root. It checks hashes,
every baseline blob and mode, the nine document inverses and one Audit addition,
refs/stashes/worktrees, actual source/check/public identities and resource caps.
It does not compile or prove native extraction. Earlier proofs, counterexamples,
repairs, marked drafts and optimized interned code remain. The full goal is active
and incomplete.
''')
files=sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(evidence).as_posix()+'\n' for p in files))
result=subprocess.run(['/usr/bin/python3',str(evidence/'verify-checkpoint.py'),'--root',str(root)],cwd=root,capture_output=True)
report=dict(exit_code=result.returncode,manifest_sha256=hashlib.sha256((evidence/'SHA256SUMS').read_bytes()).hexdigest(),manifest_entries=len(files),stdout=result.stdout.decode(),stderr=result.stderr.decode())
(area/'seal-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));assert result.returncode==0
