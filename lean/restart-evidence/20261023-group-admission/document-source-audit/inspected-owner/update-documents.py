import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
START = '591bda7cd4028ee1ed22770c9974142294c92210'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()

metrics = dict(actual_jobs=3, source_jobs=2, focused_build_jobs=0, audit_jobs=1,
    failed_jobs=0, warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0,
    selected_modules=1, public_theorems=1, audit_build_jobs=3649, audit_dependencies=75526)
for mode, live in [('normal', False), ('live', True)]:
    report = json.loads((HERE / ('proof-evidence-' + mode + '.json')).read_bytes())
    assert report['status'] == 'PASS' and report['live'] is live
    assert all(report[key] == value for key, value in metrics.items())
    assert report['audit_log_sha256'] == '786f8672ed703d466699fe5d386da0a9c5075009f78c336b1c822a6d0269bf09'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(char in '0123456789abcdef' for char in proof)
assert git('rev-parse', 'HEAD').decode().strip() == proof
assert git('rev-parse', proof + '^').decode().strip() == START
assert git('branch', '--show-current').decode().strip() == 'formalize'
selection = json.loads((HERE / 'selected-sources.json').read_bytes())
assert len(selection) == 1
assert set(git('diff-tree', '--no-commit-id', '--name-only', '-r', proof).decode().splitlines()) == set(selection) | {'lean/MicroCFTA/Audit.lean'}
for name, pin in selection.items():
    source = (ROOT / name).read_bytes()
    assert sha(source) == pin['sha256'] and len(source.splitlines()) == pin['lines']
    assert source == (HERE / (Path(name).stem + '.lean')).read_bytes()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
values = dict(now=now, proof=proof, proof_short=proof[:10])
update = (HERE / 'document-preparation/current-update.template.md').read_text().format(**values).encode()
focused = (HERE / 'document-preparation/focused-note.template.md').read_text().format(**values)
assert update.endswith(b'\n') and b'\r' not in update
assert 'H6 constructed_node_calls remains strongest combined.' in focused
assert 'No Haskell repair' in focused and 'ACTIVE and incomplete' in focused
type_summary = []
readback = json.loads((HERE / ('public-readback/group-admission-full-readback.json')).read_bytes())
for head in readback['heads']:
    short = head['head'].rsplit('.', 1)[1]
    checked = (HERE / ('public-readback/group-admission-' + short + '-public-type.txt')).read_bytes()
    printed = (HERE / ('public-readback/group-admission-' + short + '-printed-public-type.txt')).read_bytes()
    assert sha(checked) == head['checked_type_sha256'] and sha(printed) == head['printed_type_sha256']
    assert head['check_print_type_byte_identity'] is (checked == printed)
    assert head['check_print_type_lexical_identity'] and head['actual_axioms_within_standard_allowed']
    type_summary += [f"{head['head']}: {len(checked.splitlines())} TYPE lines, {len(checked)} bytes, SHA {sha(checked)}.",
        f"Printed TYPE SHA {sha(printed)}. Raw byte identity: {checked == printed}. Lexical identity: True.",
        'Actual axioms: ' + (', '.join(head['actual_axioms']) or 'none') + '.']
assert len(type_summary) == 3
focused += '\n## Selected sources and complete public types\n\n'
focused += '\n'.join(f"{name}: {pin['lines']} lines, SHA {pin['sha256']}." for name, pin in selection.items()) + '\n\n'
focused += '\n'.join(type_summary) + '\n'
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (HERE / 'haskell-repair-index.md').read_bytes()
marker = b'# Current formalization findings\n\n## Haskell fix handoff for external work\n\n' + index.rstrip() + b'\n\n'
changes = {}
for name in documents:
    original = git('show', START + ':' + name)
    assert (ROOT / name).read_bytes() == original, name
    if name == 'FINDINGS.md':
        assert original.startswith(marker)
        changed = marker + update + b'\n' + original[len(marker):]
        assert changed.startswith(marker)
    else:
        first = original.split(b'\n', 1)[0]
        prefix = first + b'\n\n'
        assert original.startswith(prefix)
        changed = prefix + update + b'\n' + original[len(prefix):]
    assert changed.replace(update + b'\n', b'', 1) == original
    changes[name] = changed
note = ROOT / 'lean/notes-current-group-admission.md'
assert not note.exists()
assert not (HERE / 'current-update.md').exists() and not (HERE / 'findings-update.md').exists()
for name, data in changes.items():
    (ROOT / name).write_bytes(data)
(HERE / 'current-update.md').write_bytes(update)
(HERE / 'findings-update.md').write_bytes(update)
note.write_text(focused)
print(json.dumps(dict(status='PASS', documents=len(changes), exact_prefix_inverses=9,
    findings_repair_index_first=True, proof=proof, focused_note=str(note.relative_to(ROOT)),
    seal_or_publication_success_claimed=False)))
