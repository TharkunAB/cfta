import gzip,hashlib,json,shutil,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-th-repair-main-20261024');evidence=root/'lean/restart-evidence/20261024-th-repair-main'
assert not evidence.exists()
for args in [('diff','--quiet'),('diff','--cached','--quiet')]:subprocess.run(['git',*args],cwd=root,check=True)
for name in ['review','seal-script-review','root-review']:assert Path('/tmp/mcfta-th-repair-main-20261024-'+name+'.md').is_file()
evidence.mkdir()
for path in sorted(area.rglob('*')):
    if not path.is_file():continue
    target=evidence/'work'/path.relative_to(area);target.parent.mkdir(parents=True,exist_ok=True)
    if path.name=='baseline-tree.txt':target.with_suffix('.txt.gz').write_bytes(gzip.compress(path.read_bytes(),mtime=0))
    else:target.write_bytes(path.read_bytes())
inputs=evidence/'inputs';inputs.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-th-repair-main-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-th-repair-main-20261024-archive-1.'):
        shutil.copyfile(path,inputs/path.name)
prior=evidence/'previous-publication';prior.mkdir()
for stem in ['archive-1','local-publication-1','authorized-push-1']:
    for suffix in ['json','log','limits.json','usage.json','source.py','peaks.txt']:
        path=Path('/tmp/mcfta-pruning-record-types-20261024-'+stem+'.'+suffix);assert path.is_file();shutil.copyfile(path,prior/path.name)
for name in ['seal-result.json','local-publication.json','remote-publication.json','push.log','publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-record-types-20261024')/name,prior/name)
shutil.copyfile('/tmp/mcfta-pruning-record-types-20261024-publication.py',prior/'publication.py')
shutil.copyfile(root/'lean/notes-current-th-repair-main.md',evidence/'current-note.md')
shutil.copyfile('/tmp/mcfta-th-repair-main-20261024-verify.py',evidence/'verify-checkpoint.py')
(evidence/'INDEX.md').write_text('''# Content-identical upstream repair integration

PR #172 merges the already checked trailing-hash generated-name repair.
The complete merge tree equals the previous pushed tree. All five upstream
repair files equal the local tested files, including mode and full bytes.
FINDINGS now marks all six recorded Haskell fixes merged. The current handoff
requires no further patch for these defects. Historical red/green evidence remains.

No Haskell or Lean source contents change. Existing strict/public/Audit and native
validation apply to the same bytes. No build or test was repeated. H6 and the
recordTypes observation guarantees retain their previous explicit boundaries.

The verifier checks the complete baseline, nine exact status insertions and the
repair-index inverse. It checks merge ancestry/tree identity, the precise upstream
five-path delta, actual native files, current handoff and resource receipts.
Previous-publication retains the proof checkpoint's post-seal publication records.
All earlier sealed evidence and optimized interned code remain unchanged.
The full formalization goal is active and incomplete.
''')
files=sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(evidence).as_posix()+'\n' for p in files))
result=subprocess.run(['/usr/bin/python3',str(evidence/'verify-checkpoint.py'),'--root',str(root)],cwd=root,capture_output=True)
report=dict(exit_code=result.returncode,manifest_sha256=hashlib.sha256((evidence/'SHA256SUMS').read_bytes()).hexdigest(),manifest_entries=len(files),stdout=result.stdout.decode(),stderr=result.stderr.decode())
(area/'seal-result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2));assert result.returncode==0
