import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-observation-20261024')
baseline = 'fe0cfe2a38ba5d7587404d89bd5fa2303f37dea6'
proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert subprocess.check_output(['git', 'rev-list', '--parents', '-n', '1', proof], cwd=root).decode().split() == [proof, baseline]
checks = json.loads((area / 'build-summary.json').read_text())
note = area / 'current-note.md'
text = note.read_text()
for marker, key in [('@INSTALLED@', 'installed_jobs'), ('@AUDIT@', 'audit_jobs'), ('@DEPENDENCIES@', 'axiom_dependency_checks')]:
    text = text.replace(marker, str(checks[key]))
assert '\nProof:' not in text
text = text.replace('Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.',
    'Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.\nProof: `' + proof + '`.')
note.write_text(text)
destination = root / 'lean/notes-current-pruning-enumeration-observation.md'
assert not destination.exists()
destination.write_bytes(note.read_bytes())
prefix = '\n## Actual pending-node observations\n\nUpdated: 2026-10-24. Main `74250bd88` is incorporated.\nProof: `PROOF_HASH`.\nRead `lean/notes-current-pruning-enumeration-observation.md`.\n\nClosed available input under Coherent derives its initial pending-slot handle.\nRealized slots and actual getUnexpandedNode reads derive complete available\nclosed Values and the full compression frame. StorageValid and allocated UVars derive finite\nactual observations. Actual reads retain StorageValid for later observations.\nRealization persists through full frames and actual native cache growth.\n\nStrict checking and the installed build pass. Audit passes AUDIT_JOBS jobs and\nDEPENDENCIES dependency checks, with one older warning and no new-source warning.\nAll six signatures and five actual axiom reports were read. Each reports only\npropext and Quot.sound. Five failed strict inputs and all reviews remain.\nThe original frozen 58-payload proposal and separate storage header remain.\n\nNext prove realization through actual allocation, intersection/assimilation and\nnarrowed slot writes. The pure intersection handle needs an actual native heap\nconnection. Prove open-hole bounds, then compose ordered reads and lazy emptiness\nwith typing, outer narrow, memo2 and typedTypes. Native extraction, global helper\ncanonicality, mutation histories, selected-current protection, cached scheduling,\nsemantic pruning, phase 4, resources, practical width, runtime/solver and\nconvergence stay open. H6 remains strongest combined. H23 stays queued.\nNo Haskell source changes. FINDINGS keeps its external repair index FIRST.\nAll six recorded fixes are on main. The full goal is ACTIVE and incomplete.\nThis record precedes evidence creation and the authorized push.\n\n'.replace('PROOF_HASH', proof).replace('AUDIT_JOBS', str(checks['audit_jobs'])).replace('DEPENDENCIES', str(checks['axiom_dependency_checks']))
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in paths:
    path = root / name
    before = path.read_text()
    assert path.read_bytes() == subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=root)
    position = before.index('## Stored enumeration-node handles') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
        before_sha256=hashlib.sha256(before.encode()).hexdigest(),
        after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
(area / 'proof-commit.json').write_text(json.dumps(dict(commit=proof, baseline=baseline,
    paths=['lean/MicroCFTA/SourcePruningEnumerationObservation.lean', 'lean/MicroCFTA/Audit.lean']), indent=2) + '\n')
print(json.dumps(dict(documents=paths, note=str(destination), proof=proof)))
