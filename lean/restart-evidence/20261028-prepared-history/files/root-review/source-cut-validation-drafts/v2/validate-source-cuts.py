from pathlib import Path
import hashlib
import json

area = Path('/tmp/mcfta-prepared-history-20261028')
repo = Path('/home/tritlo/Code/mcfta')
results = []
for owner in ['output-history', 'projection-heap', 'depth-audit']:
    folder = area / owner
    index = json.loads((folder / 'source-index.json').read_text())
    cuts = 0
    reconstructed = 0
    for record in index['sources']:
        if 'whole' in record:
            identity = record['whole']
            raw = (folder / identity['path']).read_bytes()
        else:
            identity = record['whole_identity']
            rel = Path(record['source']).relative_to(repo)
            old = (area / 'prior-documents' / rel).read_bytes()
            insertion = (area / 'document-insertions' / ('findings.md' if str(rel) == 'FINDINGS.md' else 'common.md')).read_bytes()
            first, rest = old.split(b'\n', 1)
            raw = first + b'\n' + insertion + rest
            assert raw == (repo / rel).read_bytes()
            reconstructed += 1
        assert len(raw) == identity['bytes']
        assert hashlib.sha256(raw).hexdigest() == identity['sha256']
        lines = raw.splitlines(keepends=True)
        for cut in record.get('cuts', []):
            data = (folder / cut['path']).read_bytes()
            assert len(data) == cut['bytes']
            assert hashlib.sha256(data).hexdigest() == cut['sha256']
            assert data == b''.join(lines[cut['first_line'] - 1:cut['last_line']])
            cuts += 1
    results.append(dict(owner=owner, source_records=len(index['sources']), literal_cuts=cuts,
                        reconstructed_document_sources=reconstructed))
report = dict(status='pass', results=results)
(area / 'root-review/source-cut-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
