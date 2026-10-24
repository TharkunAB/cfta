import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-generated-views-20261024')
evidence=root/'lean/restart-evidence/20261024-generated-node-views'
assert not evidence.exists()
for name in ['independent-source-review','formal-coverage-review','test-review','document-review','root-review']:
    assert Path('/tmp/mcfta-generated-views-20261024-'+name+'.md').is_file()
evidence.mkdir()
for path in sorted(area.rglob('*')):
    if not path.is_file():continue
    target=evidence/'work'/path.relative_to(area);target.parent.mkdir(parents=True,exist_ok=True)
    data=path.read_bytes()
    if path.name=='baseline-tree.txt':target.with_suffix('.txt.gz').write_bytes(gzip.compress(data,mtime=0))
    else:target.write_bytes(data)
inputs=evidence/'inputs';inputs.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-generated-views-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-generated-views-20261024-archive-1.'):
        shutil.copyfile(path,inputs/path.name)
review_inputs=Path('/tmp/mcfta-generated-views-20261024-review-inputs')
assert review_inputs.is_dir()
shutil.copytree(review_inputs,evidence/'review-inputs')
prior=evidence/'previous-publication';prior.mkdir()
for stem in ['archive-1','local-publication-1','authorized-push-1']:
    for suffix in ['json','log','limits.json','usage.json','source.py','peaks.txt']:
        path=Path('/tmp/mcfta-template-oracle-20261024-'+stem+'.'+suffix)
        assert path.is_file(),path
        shutil.copyfile(path,prior/path.name)
for name in ['seal-result.json','local-publication.json','remote-publication.json','push.log','publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-template-oracle-20261024')/name,prior/name)
shutil.copyfile('/tmp/mcfta-template-oracle-20261024-publication.py',prior/'publication.py')
upstream=evidence/'upstream-sources'
for name in json.loads((area/'merge-report.json').read_text())['changed_paths']:
    target=upstream/name;target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(root/name,target)
shutil.copyfile(root/'lean/notes-current-generated-node-views.md',evidence/'current-note.md')
shutil.copyfile('/tmp/mcfta-generated-views-20261024-verify.py',evidence/'verify-checkpoint.py')
(evidence/'INDEX.md').write_text('''# Generated scalar node view integration evidence

Main c4f7319 and merge a7d667f add cfta-th. Read current-note.md for source
behavior, fresh checks and the explicit generated-view proof obligations.
Four Hspec examples passed. The refinement example does not check rank.
The preceding Lean source bytes are unchanged. No new Haskell repair is needed.

Work retains the pre-merge tree identity, refs, worktrees, stashes, exact upstream
diff, merge report and all four fresh validation commands and raw outputs.
Inputs retain the root and independent reviews and actual resource receipts.
Upstream-sources retains all ten changed paths. Review-inputs pins source reads.
Previous-publication retains the prior proof checkpoint's post-seal receipts.

Run verify-checkpoint.py with --root set to the repository root. It checks the
complete manifest and every original baseline blob and mode. The only permitted
old-file changes are three exact upstream files and nine status insertions.
It also checks the seven new upstream files, main ancestry, refs, worktrees,
stashes, raw validation identities and resource limits. It does not compile,
execute Template Haskell or prove native extraction. All earlier formalization
work remains. The complete goal remains active and incomplete.
''')
files=sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(evidence).as_posix()+'\n' for p in files))
result=subprocess.run(['/usr/bin/python3',str(evidence/'verify-checkpoint.py'),'--root',str(root)],cwd=root,capture_output=True)
report=dict(exit_code=result.returncode,manifest_sha256=hashlib.sha256((evidence/'SHA256SUMS').read_bytes()).hexdigest(),manifest_entries=len(files),stdout=result.stdout.decode(),stderr=result.stderr.decode())
(area/'seal-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));assert result.returncode==0
