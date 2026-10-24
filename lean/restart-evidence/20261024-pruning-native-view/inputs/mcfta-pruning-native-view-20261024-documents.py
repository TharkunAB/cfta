import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-native-view-20261024')
baseline = '4c52896ccff16f4fbf479ac33746b6dbdf438e35'
proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert subprocess.check_output(['git', 'rev-list', '--parents', '-n', '1', proof], cwd=root).decode().split() == [proof, baseline]
note = area / 'current-note.md'
text = note.read_text()
assert '\nProof:' not in text
text = text.replace('Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.',
    'Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.\nProof: `' + proof + '`.')
note.write_text(text)
destination = root / 'lean/notes-current-pruning-native-view.md'
assert not destination.exists()
destination.write_bytes(note.read_bytes())
prefix = '''
## Actual interned-node narrowing and emptiness

Updated: 2026-10-24. Main `74250bd88` is incorporated.
Proof: `PROOF_HASH`.
Read `lean/notes-current-pruning-native-view.md`.

The concrete source filter, repaired reader and actual smart constructor now
derive finite narrowing from an initially Ready cache and closed available input. The final
cache retains validity and issued-name history. Exact normalized rows and the
empty-result equivalence are proved. The actual second read retains the final
cache. Non-Mu emptyAt derives its Boolean result; Mu alone returns false without
a read. Union stays in the actual narrowing path. Full symbols and edges remain.

Strict checking and the installed build pass. Audit passes 3679 jobs and 76089
dependency checks, with one older warning and no new-source warning. All six
signatures and three actual axiom reports were read; only the standard three
Lean axioms occur. Failed inputs and the original frozen proposal remain.

Next connect enumeration IDs to stored interned Values and cache histories,
then compose the outer narrow wrapper, actual typing and memo2 with typedTypes.
The semantic laws of fits/admits, global helper canonicality, mutation histories,
selected-current protection, cached scheduling, semantic pruning, phase 4,
resources, practical width, runtime/solver and convergence remain open.
H6 remains strongest combined. H23 stays queued. No Haskell source changes.
FINDINGS keeps its external repair index FIRST. All six recorded fixes are on
main. The full goal is ACTIVE and incomplete. This precedes evidence and push.

'''.replace('PROOF_HASH', proof)
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in paths:
    path = root / name
    before = path.read_text()
    assert path.read_bytes() == subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=root)
    position = before.index('## Generated-name repair merged on main') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
        before_sha256=hashlib.sha256(before.encode()).hexdigest(),
        after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
(area / 'proof-commit.json').write_text(json.dumps(dict(commit=proof, baseline=baseline,
    paths=['lean/MicroCFTA/SourcePruningNativeView.lean', 'lean/MicroCFTA/Audit.lean']), indent=2) + '\n')
print(json.dumps(dict(documents=paths, note=str(destination), proof=proof)))
