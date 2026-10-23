exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import difflib
import shutil
owner = Path('/tmp/mcfta-cluster-admission-publication-preparation')
assert not owner.exists()
owner.mkdir()
basis = ROOT / 'lean/restart-evidence/20261023-comparison-native-covered/final-publication.py'
before = basis.read_text()
after = before.replace('20261023-comparison-native-covered', '20261023-cluster-admission')
after = after.replace('b796e8e660a73ac328d41cad53c61099ba79d93f', START)
after = after.replace('codex/backup-comparison-native-covered-20261023-0601', 'codex/backup-cluster-admission-20261023-0712')
after = after.replace('notes-current-comparison-native-covered.md', 'notes-current-cluster-admission.md')
after = after.replace('Preserve original-row comparison coverage evidence', 'Preserve cluster admission proof evidence')
after = after.replace('mcfta-comparison-native-covered-local-publication.json', 'mcfta-cluster-admission-local-publication.json')
assert len(before.splitlines()) == len(after.splitlines()) == 47 and 'comparison-native-covered' not in after
(owner / 'final-publication.basis.py').write_text(before)
(owner / 'final-publication.py').write_text(after)
(owner / 'publication.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile='basis/final-publication.py', tofile='selected/final-publication.py')))
(owner / 'publication.inverse.patch').write_text(''.join(difflib.unified_diff(after.splitlines(True), before.splitlines(True), fromfile='selected/final-publication.py', tofile='basis/final-publication.py')))
shutil.copy2(Path('/tmp/mcfta-cluster-admission-proof-commit.py'), owner / 'proof-commit.py')
(owner / 'scope.md').write_text('Root authored this small proof committer and adapted the sealed H28 local publisher. The proof committer requires both actual proof-verification modes and the independently accepted source/history gate before staging exactly three modules and Audit. The publisher retains every H28 seal, branch, backup, main/origin-main, scoped staging, older sealed-path index presence, complete filesystem/index/HEAD blob/mode equality and clean-tree guard. Only checkpoint literals change. Both commit messages contain only the change description. The publisher executes no network command. Root performs the standing authorized formalize push separately after actual seal/publication acceptance. No program execution is authorized by this preparation.\n')
pins = [dict(path=path.name, bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.iterdir())]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_LOCAL_PUBLICATION_SOURCE_PENDING_INDEPENDENT_REVIEW', pins_sha256=sha(owner / 'pins.json'), publisher_lines=47, proof_committer_lines=28, no_future_writes=True), indent=2) + '\n')
print(json.dumps(dict(pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'), publisher_sha256=sha(owner / 'final-publication.py'), committer_sha256=sha(owner / 'proof-commit.py'))))
