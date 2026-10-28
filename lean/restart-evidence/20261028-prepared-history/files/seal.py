from pathlib import Path
import datetime
import hashlib
import json
import subprocess

area = Path('/tmp/mcfta-prepared-history-20261028')
repo = Path('/home/tritlo/Code/mcfta')


def digest(data):
    return hashlib.sha256(data).hexdigest()


owners = []
for name in ['output-history', 'projection-heap', 'depth-audit']:
    folder = area / name
    seal = json.loads((folder / 'FROZEN.json').read_text())
    assert seal['status'] == 'FROZEN' and seal['write_halt']
    pins_raw = (folder / 'pins.json').read_bytes()
    assert len(pins_raw) == seal['pins_bytes']
    assert digest(pins_raw) == seal['pins_sha256']
    pins = json.loads(pins_raw)['payloads']
    expected = {record['path'] for record in pins} | {'pins.json', 'FROZEN.json'}
    assert {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()} == expected
    for record in pins:
        raw = (folder / record['path']).read_bytes()
        assert len(raw) == record['bytes'] and digest(raw) == record['sha256']
    owners.append(dict(owner=name, files=len(expected), payloads=len(pins),
                       pins_sha256=digest(pins_raw), seal_sha256=digest((folder / 'FROZEN.json').read_bytes())))

subprocess.run(['python3', str(area / 'root-review/validate-source-cuts.py')], check=True)
subprocess.run(['python3', str(area / 'validate.py')], check=True)
subprocess.run(['python3', str(area / 'public-validation.py')], check=True)
inverse = json.loads((area / 'document-inverse.json').read_text())
for name, record in inverse.items():
    old = (area / 'prior-documents' / name).read_bytes()
    insertion = (area / 'document-insertions' / ('findings.md' if name == 'FINDINGS.md' else 'common.md')).read_bytes()
    first, rest = old.split(b'\n', 1)
    current = first + b'\n' + insertion + rest
    assert digest(old) == record['before_sha256'] and digest(current) == record['after_sha256']
    assert current.replace(insertion, b'', 1) == old and current == (repo / name).read_bytes()
assert (area / 'root-review/notes-current-prepared-history.md').read_bytes() == (repo / 'lean/notes-current-prepared-history.md').read_bytes()
subprocess.run(['git', 'diff', '--check'], cwd=repo, check=True)
head = (area / 'source-head.txt').read_text().strip()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo).decode().strip() == head
publication = json.loads((area / 'mcfta-prepared-history-source-publication.json').read_text())
assert publication['head'] == publication['remote_head'] == publication['tracking_head'] == head
assert publication['branch'] == 'refs/heads/formalize'
assert publication['destination'] == 'git@github.com:TharkunAB/cfta.git'

review = dict(status='pass', source_head=head, goal_status='active', full_formalization_complete=False,
              owner_seals=owners, document_inverses=len(inverse),
              root_read_scope='Every new source and final corrective diff; all four failed compiler logs; all owner final reports; complete final note and insertions. Assigned public appendix blocks were read by the named owners. Root does not claim a whole read of the public appendix or old giant document bodies.',
              proof_scope='Operational history for every actual prepared output; initial checked construction and completed rich-query heap projection; conditional prepared-parent backward helper; actual completed-head resource receipt. Whole semantic/resource history attachment, global sufficient depth, coverage and physical Haskell correspondence remain open.',
              noncompiler_validation_failures='Two root source-cut schema attempts failed before the final schema-aware validator passed. Their records and predecessor script are retained. These are separate from the four failed strict Lean attempts.')
(area / 'root-review/final-review.json').write_text(json.dumps(review, indent=2) + '\n')
assert not (area / 'FROZEN.json').exists()
payloads = []
for path in sorted(area.rglob('*')):
    if path.is_file():
        assert not path.is_symlink()
        raw = path.read_bytes()
        payloads.append(dict(path=path.relative_to(area).as_posix(), bytes=len(raw), sha256=digest(raw)))
frozen = dict(status='FROZEN', measured_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              source_head=head, goal_status='active', full_formalization_complete=False,
              owner_seals=owners, write_halt=True, payloads=payloads)
(area / 'FROZEN.json').write_text(json.dumps(frozen, indent=2) + '\n')
assert {p.relative_to(area).as_posix() for p in area.rglob('*') if p.is_file()} == {p['path'] for p in payloads} | {'FROZEN.json'}
print(json.dumps(dict(status='frozen', files=len(payloads) + 1, owner_seals=owners)))
