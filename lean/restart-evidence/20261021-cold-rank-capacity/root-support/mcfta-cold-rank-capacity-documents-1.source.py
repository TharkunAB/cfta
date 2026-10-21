import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261021-cold-rank-capacity'
for source, destination, verifier in [
    ('/tmp/mcfta-cold-rank-semantic-proof', 'cold-semantic', 'cold-rank-semantic-verify.py'),
    ('/tmp/mcfta-cold-rank-semantic-independent-review', 'semantic-independent-review', 'review-verify.py'),
]:
    subprocess.run(['/usr/bin/python3', str(here / 'archive-component.py'),
                    source, destination, verifier], check=True)

assessment = Path('/tmp/mcfta-after-cold-semantic-assessment')
target = here / 'next-gap-assessment'
assert not target.exists()
shutil.copytree(assessment, target)
index = json.loads((target / 'source-index.json').read_text())
snapshots = []
for entry in index['sources'] + index['external_source_cuts']:
    original = Path(entry['path']) if Path(entry['path']).is_absolute() else root / entry['path']
    data = original.read_bytes()
    assert hashlib.sha256(data).hexdigest() == entry['source_sha256']
    lines = data.splitlines(True)
    assert len(lines) == entry['lines']
    for span in entry['ranges']:
        assert 1 <= span['start'] <= span['end'] <= len(lines)
        part = b''.join(lines[span['start'] - 1:span['end']])
        assert part == (target / span['excerpt']).read_bytes()
        assert hashlib.sha256(part).hexdigest() == span['sha256']
    name = 'full-read-cuts/' + entry['id'] + '.source.txt'
    snapshot = target / name
    snapshot.parent.mkdir(exist_ok=True)
    snapshot.write_bytes(data)
    snapshots.append(dict(id=entry['id'], original=entry['path'], snapshot=name,
                          bytes=len(data), sha256=entry['source_sha256']))
(target / 'root-source-snapshots.json').write_text(json.dumps(dict(
    snapshots=snapshots, personally_read_note_and_all_cited_ranges=True,
    historical_document_and_external_read_cuts_retained=True,
    new_proof_jobs=0, observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat()), indent=2) + '\n')

subprocess.run(['/usr/bin/python3', str(here / 'prepare-checkpoint.py')], check=True)
modules = {}
for tag, prefix in [('cold-capacity', 'cold-rank-capacity'), ('cold-semantic', 'cold-rank-semantic')]:
    selected = json.loads((here / tag / (prefix + '-selection.json')).read_text())
    relative = tag + '/' + selected['selected_public'] + '.log'
    full = (here / relative).read_bytes()
    assert len(full) == selected['public_log_bytes']
    assert hashlib.sha256(full).hexdigest() == selected['public_log_sha256']
    modules[tag] = dict(source_sha256=selected['source_sha256'], source_lines=selected['source_lines'],
                        full_relative_path=relative, full_bytes=len(full),
                        full_sha256=selected['public_log_sha256'])
result = dict(actual_jobs=10, failed_jobs=1, audit_jobs=3619, audit_dependencies=75218,
              modules=modules, completion_claimed=False)
(here / 'checkpoint-result.json').write_text(json.dumps(result, indent=2) + '\n')
subprocess.run(['/usr/bin/python3', str(here / 'update-documents.py')], check=True)
print(json.dumps(dict(status='DOCUMENTS_AND_EVIDENCE_PREPARED', new_proof_jobs=0)))
