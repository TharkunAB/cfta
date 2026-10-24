import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-reread-20261024')
baseline = '65d32756024b591ed57cd695d7cf777b3ff6ab63'
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
destination = root / 'lean/notes-current-pruning-enumeration-reread.md'
assert not destination.exists()
destination.write_bytes(note.read_bytes())
prefix = """
## Actual pending-node representative rereads

Updated: 2026-10-24. Main `74250bd88` is incorporated.
Proof: `PROOF_HASH`.
Read `lean/notes-current-pruning-enumeration-reread.md`.

An actual pending read and an intervening full frame derive a finite actual
representative reread at the same root. Its actual compressed state, full
frames, old handle, ordered suspended list and slot bound are retained.
An actual false recursion check also retains the complete frame.
No Safe, Ready, StorageValid, supplied root or second success is assumed.

The second strict input passes with an empty log after the StateT.pure-only
repair. The failed first input remains. The installed build passes.
Audit passes AUDIT_JOBS jobs and DEPENDENCIES dependency checks, with one older
warning and no new-source warning. Both complete signatures and actual axiom
reports were read. Each reports only propext and Quot.sound.
The 62-line module adds two theorems. All 51 frozen payloads remain.

Next compose actual narrowing with both heap and enumeration-state effects.
Preserve Empty rejection, equal handles, the actual second representative read
and its actual compressed state before the changed write. Keep the original
raw UVar in typing and holeKey tests. The changed write updates values.
Native cached indices, intersection/assimilation, open-hole bounds, ordered
reads, lazy emptiness, typing, outer narrow, memo2 and typedTypes remain open.
Global helper canonicality, mutation histories, selected-current protection,
cached scheduling, semantic pruning, phase 4, resources, practical width,
native extraction, runtime/solver and convergence stay open. H6 remains
strongest combined. H23 stays queued. No Haskell source changes. FINDINGS keeps
its external repair index FIRST. All six recorded fixes are on main.
The full goal is ACTIVE and incomplete. This record precedes evidence and push.

""".replace('PROOF_HASH', proof).replace('AUDIT_JOBS', str(checks['audit_jobs'])).replace('DEPENDENCIES', str(checks['axiom_dependency_checks']))
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in paths:
    path = root / name
    before = path.read_text()
    assert path.read_bytes() == subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=root)
    position = before.index('## Enumeration handle identity') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
        before_sha256=hashlib.sha256(before.encode()).hexdigest(),
        after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
(area / 'proof-commit.json').write_text(json.dumps(dict(commit=proof, baseline=baseline,
    paths=['lean/MicroCFTA/SourcePruningEnumerationReread.lean', 'lean/MicroCFTA/Audit.lean']), indent=2) + '\n')
print(json.dumps(dict(documents=paths, note=str(destination), proof=proof)))
