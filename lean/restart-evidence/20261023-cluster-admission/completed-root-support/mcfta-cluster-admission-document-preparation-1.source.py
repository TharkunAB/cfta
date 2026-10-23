exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
owner = Path('/tmp/mcfta-cluster-admission-document-preparation')
assert not owner.exists()
owner.mkdir()
for source_name, target_name in [
    ('mcfta-cluster-admission-update-documents.py', 'update-documents.py'),
    ('mcfta-cluster-admission-current-update.proposal.md', 'current-update.template.md'),
    ('mcfta-cluster-admission-focused-note.proposal.md', 'focused-note.template.md'),
]:
    shutil.copy2(Path('/tmp') / source_name, owner / target_name)
(owner / 'scope.md').write_text('Root authored this document writer and both prose templates. The writer requires both actual standalone proof-evidence modes before any document write. The proof verifier checks complete raw proof evidence. This writer checks the passed report, exact four-file proof commit, selected source identity and raw TYPE metrics before writing nine reversible LF prefixes and the focused note. FINDINGS keeps the unchanged Haskell repair index first. Actual preservation and final document review remain required before seal/publication. No seal or publication result is claimed. No writer execution is authorized by this package.\n')
pins = [dict(path=path.name, bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.iterdir())]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_DOCUMENT_SOURCE_PENDING_INDEPENDENT_REVIEW', pins_sha256=sha(owner / 'pins.json'), writer_lines=89, no_future_writes=True), indent=2) + '\n')
print(json.dumps(dict(pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'), writer_sha256=sha(owner / 'update-documents.py'))))
