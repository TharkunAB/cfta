import gzip,hashlib,json,shutil,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-pruning-record-types-20261024')
evidence=root/'lean/restart-evidence/20261024-pruning-record-types';assert not evidence.exists()
for args in [('diff','--quiet'),('diff','--cached','--quiet')]:subprocess.run(['git',*args],cwd=root,check=True)
for name in ['source-review','model-review','positions-review','final-delta-review','public-review','document-review','seal-script-review','root-review']:
    assert Path('/tmp/mcfta-pruning-record-types-20261024-'+name+'.md').is_file()
evidence.mkdir()
for path in sorted(area.rglob('*')):
    if not path.is_file():continue
    target=evidence/'work'/path.relative_to(area);target.parent.mkdir(parents=True,exist_ok=True)
    if path.name=='baseline-tree.txt':target.with_suffix('.txt.gz').write_bytes(gzip.compress(path.read_bytes(),mtime=0))
    else:target.write_bytes(path.read_bytes())
inputs=evidence/'inputs';inputs.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-pruning-record-types-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-record-types-20261024-archive-1.'):
        shutil.copyfile(path,inputs/path.name)
shutil.copytree('/tmp/mcfta-pruning-positions-20261024-proposal',evidence/'helper-proposal')
prior=evidence/'previous-publication';prior.mkdir()
for stem in ['archive-1','local-publication-1','authorized-push-1']:
    for suffix in ['json','log','limits.json','usage.json','source.py','peaks.txt']:
        path=Path('/tmp/mcfta-derived-scalar-shape-20261024-'+stem+'.'+suffix);assert path.is_file();shutil.copyfile(path,prior/path.name)
for name in ['seal-result.json','local-publication.json','remote-publication.json','push.log','publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-derived-scalar-shape-20261024')/name,prior/name)
shutil.copyfile('/tmp/mcfta-derived-scalar-shape-20261024-publication.py',prior/'publication.py')
production=evidence/'production-sources';production.mkdir()
for name in ['SourcePruningPositions','SourcePruningRecordTypes']:
    shutil.copyfile(root/'lean/MicroCFTA'/(name+'.lean'),production/(name+'.lean'))
shutil.copyfile(root/'lean/notes-current-pruning-record-types.md',evidence/'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-record-types-20261024-native-node-view-plan.md',evidence/'next-native-node-view-plan.md')
shutil.copyfile('/tmp/mcfta-pruning-record-types-20261024-verify.py',evidence/'verify-checkpoint.py')
(evidence/'INDEX.md').write_text('''# Pruning position and callback observation evidence

Read current-note.md for the exact source contracts and remaining obligations.
The helpers retain full symbols, child order, raw IDs and repeated program holes.
The concrete recordTypes callback retains metadata and the complete compression
frame, successful result agreement, fuel retention and finite transport.
This does not prove semantic pruning or full typedTypes correspondence.

Work retains the complete baseline and all eleven Lean/build/public attempts.
Six helper attempts include the first import-path setup failure and later
termination/equation failures. Both callback attempts retain the proof repair.
The final strict helper and callback logs are empty. Inputs retain complete root
and independent reviews, exact commands, fresh allowance and capped 4 GiB/no-swap
receipts. The frozen source-only helper proposal remains unchanged.
The native-node-view plan retains the Mu-only distinction, actual closure/smart
constructor/cache requirements and missing enumeration-ID realization.
Previous-publication retains the prior checkpoint's post-seal publication receipts.

Run verify-checkpoint.py with --root set to the repository root. It checks the
manifest, every baseline blob/mode, nine exact document inverses, one Audit
import, frozen helper inputs, actual source/public identities and raw receipts.
It does not compile or prove native extraction, canonicality or semantic pruning.
Earlier proofs, counterexamples, repairs, drafts and optimized interned code remain.
FINDINGS keeps the complete external Haskell repair index first. No Haskell
source changes. The full goal remains active and incomplete.
''')
files=sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(evidence).as_posix()+'\n' for p in files))
result=subprocess.run(['/usr/bin/python3',str(evidence/'verify-checkpoint.py'),'--root',str(root)],cwd=root,capture_output=True)
report=dict(exit_code=result.returncode,manifest_sha256=hashlib.sha256((evidence/'SHA256SUMS').read_bytes()).hexdigest(),manifest_entries=len(files),stdout=result.stdout.decode(),stderr=result.stderr.decode())
(area/'seal-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));assert result.returncode==0
