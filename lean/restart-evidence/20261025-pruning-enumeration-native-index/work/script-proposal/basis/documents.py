import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-terminal-20261024')
baseline = '04822017ec505dd481a7c67979c77655cb1fec70'
proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert subprocess.check_output(['git', 'rev-list', '--parents', '-n', '1', proof], cwd=root).decode().split() == [proof, baseline]
checks = json.loads((area / 'build-summary.json').read_text())
replacements = {
    '@PROOF@': proof,
    '@INSTALLED@': str(checks['installed_jobs']),
    '@AUDIT@': str(checks['audit_jobs']),
    '@DEPENDENCIES@': str(checks['axiom_dependency_checks']),
    '@VALIDATION@': checks['validation_text'],
    '@AXIOMS@': checks['axiom_text'],
}
def expand(text):
    for marker, replacement in replacements.items():
        text = text.replace(marker, replacement)
    assert '@' not in text
    return text
note = expand((area / 'current-note.md').read_text())
note = note.replace('Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.',
    'Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.\nProof: `' + proof + '`.')
destination = root / 'lean/notes-current-pruning-enumeration-terminal.md'
assert not destination.exists()
destination.write_text(note)
(area / 'current-note.md').write_text(note)
prefix = expand((area / 'status-prefix.txt').read_text())
(area / 'status-prefix.txt').write_text(prefix)
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in paths:
    path = root / name
    before = path.read_text()
    assert path.read_bytes() == subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=root)
    position = before.index('## Storage and waiting counts through the checked fold') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
        before_sha256=hashlib.sha256(before.encode()).hexdigest(),
        after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
(area / 'proof-commit.json').write_text(json.dumps(dict(commit=proof, baseline=baseline,
    paths=['lean/MicroCFTA/SourcePruningEnumerationTerminal.lean', 'lean/MicroCFTA/Audit.lean']), indent=2) + '\n')
print(json.dumps(dict(documents=paths, note=str(destination), proof=proof)))
