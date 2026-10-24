import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-writes-20261024')
baseline = '597dc875e576d348073d03c49e3aa8ab523b33c3'
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
destination = root / 'lean/notes-current-pruning-enumeration-writes.md'
assert not destination.exists()
destination.write_bytes(note.read_bytes())
prefix = '\n## Encoded enumeration-slot writes\n\nUpdated: 2026-10-24. Main `74250bd88` is incorporated.\nProof: `PROOF_HASH`.\nRead `lean/notes-current-pruning-enumeration-writes.md`.\n\nCoherent/Available/closed inputs and incoming realization derive the exact\ncomputed handle for actual allocation or raw slot replacement. Alignment gives\nthe returned allocation slot. An in-range raw address gives exact replacement.\nBoth operations retain realization of every pending slot and the full modeled\nstate effects. The native heap stays the same. Suspended lists remain intact.\n\nStrict checking passes on the first attempt with an empty log. The installed\nbuild passes. Audit passes AUDIT_JOBS jobs and DEPENDENCIES dependency checks, with\none older warning and no new-source warning. Both signatures and both actual\naxiom reports were read. Each reports only propext and Quot.sound.\nThe 69-line module adds two theorems. Its frozen 42-payload owner remains.\n\nNext compose actual native narrowing, retaining Empty rejection, the actual\nheap and the unchanged-ID branch. General intersection/assimilation needs its\nnative handle/heap connection. Native cached-index maintenance, open-hole bounds,\nordered reads, lazy emptiness, typing, outer narrow, memo2 and typedTypes remain.\nGlobal helper canonicality, mutation histories, selected-current protection,\ncached scheduling, semantic pruning, phase 4, resources, practical width,\nruntime/solver and convergence stay open. H6 remains strongest combined.\nH23 stays queued. No Haskell source changes. FINDINGS keeps its external repair\nindex FIRST. All six recorded fixes are on main. The full goal is ACTIVE and\nincomplete. This record precedes evidence creation and the authorized push.\n\n'.replace('PROOF_HASH', proof).replace('AUDIT_JOBS', str(checks['audit_jobs'])).replace('DEPENDENCIES', str(checks['axiom_dependency_checks']))
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in paths:
    path = root / name
    before = path.read_text()
    assert path.read_bytes() == subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=root)
    position = before.index('## Actual pending-node observations') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
        before_sha256=hashlib.sha256(before.encode()).hexdigest(),
        after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
(area / 'proof-commit.json').write_text(json.dumps(dict(commit=proof, baseline=baseline,
    paths=['lean/MicroCFTA/SourcePruningEnumerationWrites.lean', 'lean/MicroCFTA/Audit.lean']), indent=2) + '\n')
print(json.dumps(dict(documents=paths, note=str(destination), proof=proof)))
