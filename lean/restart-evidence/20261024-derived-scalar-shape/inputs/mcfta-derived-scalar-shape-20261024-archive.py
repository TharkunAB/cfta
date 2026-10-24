import gzip,hashlib,json,shutil,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-derived-scalar-shape-20261024')
evidence=root/'lean/restart-evidence/20261024-derived-scalar-shape';assert not evidence.exists()
for name in ['name-repair-review','haskell-repair-review','model-review','proof-repair-review','elaboration-review','public-review','document-review','root-review']:
    assert Path('/tmp/mcfta-derived-scalar-shape-20261024-'+name+'.md').is_file()
evidence.mkdir()
for path in sorted(area.rglob('*')):
    if not path.is_file():continue
    target=evidence/'work'/path.relative_to(area);target.parent.mkdir(parents=True,exist_ok=True)
    if path.name=='baseline-tree.txt':target.with_suffix('.txt.gz').write_bytes(gzip.compress(path.read_bytes(),mtime=0))
    else:target.write_bytes(path.read_bytes())
inputs=evidence/'inputs';inputs.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-derived-scalar-shape-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-derived-scalar-shape-20261024-archive-1.'):
        shutil.copyfile(path,inputs/path.name)
shutil.copyfile('/tmp/mcfta-typed-observer-20261024-plan.md',evidence/'next-typed-observer-plan.md')
shutil.copytree('/tmp/mcfta-generated-views-shape-20261024-proposal',evidence/'pre-repair-proposal')
prior=evidence/'previous-publication';prior.mkdir()
for stem in ['archive-2','local-publication-1','authorized-push-1']:
    for suffix in ['json','log','limits.json','usage.json','source.py','peaks.txt']:
        path=Path('/tmp/mcfta-generated-views-20261024-'+stem+'.'+suffix);assert path.is_file();shutil.copyfile(path,prior/path.name)
for name in ['seal-result.json','local-publication.json','remote-publication.json','push.log','publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-generated-views-20261024')/name,prior/name)
shutil.copyfile('/tmp/mcfta-generated-views-20261024-publication.py',prior/'publication.py')
for name in json.loads((area/'native-repair-pins.json').read_text()):
    if name=='FINDINGS.md':continue
    target=evidence/'native-repair-sources'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/name,target)
shutil.copyfile(root/'lean/MicroCFTA/SourceGeneratedNodeViewShape.lean',evidence/'production-source.lean')
shutil.copyfile(root/'lean/notes-current-derived-scalar-shape.md',evidence/'current-note.md')
shutil.copyfile('/tmp/mcfta-derived-scalar-shape-20261024-verify.py',evidence/'verify-checkpoint.py')
(evidence/'INDEX.md').write_text('''# Generated scalar shape and trailing-hash repair evidence

Read current-note.md for the exact proof contracts and native repair. The model
checks observed declaration descriptors, name criteria and scalar shapes. It
preserves constructor order and conditional first-error behavior. It does not
verify TH/GHC extraction, Generic realization, build/read laws or source codecs.

Work retains the pre-change baseline, native controlled failures, distinguishing
old-producer regressions, repaired validation and every Lean attempt. The first
strict check and unfiltered HLint suggestion remain. Inputs retain root and
independent reviews, exact commands, fresh allowance and 4 GiB/no-swap receipts.
The source-only pre-repair proposal remains unchanged. Native-repair-sources
pins the exact five Haskell/package changes. The next typed-observer plan retains
the Mu-only distinction and ordered raw-ID/state requirements. Previous-publication
retains the prior checkpoint's post-seal publication receipts and exact payload.

Run verify-checkpoint.py with --root set to the repository root. It checks the
manifest, every baseline blob and mode, exact repair and document inverses, one
Audit import, actual source/public identities, raw validations and resource caps.
It does not compile or prove native extraction. Earlier proofs, counterexamples,
repairs, drafts and optimized interned code remain. The full goal is active and
incomplete. The sixth Haskell repair still requires an upstream import.
''')
files=sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(evidence).as_posix()+'\n' for p in files))
result=subprocess.run(['/usr/bin/python3',str(evidence/'verify-checkpoint.py'),'--root',str(root)],cwd=root,capture_output=True)
report=dict(exit_code=result.returncode,manifest_sha256=hashlib.sha256((evidence/'SHA256SUMS').read_bytes()).hexdigest(),manifest_entries=len(files),stdout=result.stdout.decode(),stderr=result.stderr.decode())
(area/'seal-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));assert result.returncode==0
