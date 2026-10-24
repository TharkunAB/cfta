import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-identity-20261024')
baseline = '25d27d16e5cb3b9cf5d1c5f3371c14dd55822d2e'
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
destination = root / 'lean/notes-current-pruning-enumeration-identity.md'
assert not destination.exists()
destination.write_bytes(note.read_bytes())
prefix = """
## Enumeration handle identity

Updated: 2026-10-24. Main `74250bd88` is incorporated.
Proof: `PROOF_HASH`.
Read `lean/notes-current-pruning-enumeration-identity.md`.

A coherent successful decoder lookup derives the same encoded handle for the
complete stored Value. No availability or closedness premise is needed.
All-fuel narrowing of Empty returns Empty and retains the same native heap.
These results close two prerequisites for the actual narrowing action.

Strict checking and the installed build pass. Audit passes AUDIT_JOBS jobs and
DEPENDENCIES dependency checks, with one older warning and no new-source warning.
Both actual signatures and axiom reports were read. AXIOM_TEXT
The SOURCE_LINES-line module adds two theorems. Original frozen identity and
separately reviewed additive Empty declarations remain intact.

Next compose actual narrowing with the incoming pending-slot realization and
all final heap effects. Preserve Empty rejection and the unchanged-ID branch.
The changed branch must use the actual second representative read and its
compression frame before the write. Keep the original raw UVar in typing tests.
Native cached indices, intersection/assimilation, open-hole bounds, ordered
reads, lazy emptiness, typing, outer narrow, memo2 and typedTypes remain open.
Global helper canonicality, mutation histories, selected-current protection,
cached scheduling, semantic pruning, phase 4, resources, practical width,
runtime/solver and convergence stay open. H6 remains strongest combined.
H23 stays queued. No Haskell source changes. FINDINGS keeps its external repair
index FIRST. All six recorded fixes are on main. The full goal is ACTIVE and
incomplete. This record precedes evidence creation and the authorized push.

""".replace('PROOF_HASH', proof).replace('AUDIT_JOBS', str(checks['audit_jobs'])).replace('DEPENDENCIES', str(checks['axiom_dependency_checks'])).replace('AXIOM_TEXT', checks['axiom_text']).replace('SOURCE_LINES', str(checks['source_lines']))
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in paths:
    path = root / name
    before = path.read_text()
    assert path.read_bytes() == subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=root)
    position = before.index('## Encoded enumeration-slot writes') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
        before_sha256=hashlib.sha256(before.encode()).hexdigest(),
        after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
(area / 'proof-commit.json').write_text(json.dumps(dict(commit=proof, baseline=baseline,
    paths=['lean/MicroCFTA/SourcePruningEnumerationIdentity.lean', 'lean/MicroCFTA/Audit.lean']), indent=2) + '\n')
print(json.dumps(dict(documents=paths, note=str(destination), proof=proof)))
