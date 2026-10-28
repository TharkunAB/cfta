from pathlib import Path
import difflib
import hashlib
import json

area = Path('/tmp/mcfta-prepared-recursive-20261028')
own = area / 'original-opaque-model-review'
repo = Path('/home/tritlo/Code/mcfta')
assert not (own / 'FROZEN.json').exists()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def ident(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha(data)}


index = json.loads((own / 'source-index.json').read_text())
corrections = []
for original, historical, final, full_read in [
    (repo / 'lean/notes-current-prepared-recursive.md',
     own / 'documents/lean/notes-current-prepared-recursive.md',
     own / 'documents/final-corrected/lean/notes-current-prepared-recursive.md', True),
    (area / 'document-validation.json',
     own / 'evidence/final/document-validation.json',
     own / 'evidence/final-corrected/document-validation.json', False),
]:
    old, new = historical.read_bytes(), original.read_bytes()
    assert old != new
    final.parent.mkdir(parents=True, exist_ok=True)
    final.write_bytes(new)
    for row in index['sources']:
        if row['source'] == str(original):
            assert row['whole']['sha256'] == sha(old)
            row['historical_external_source'] = row['source']
            row['source'] = str(historical)
            row['read_scope'] += ' PRE-CORRECTION historical snapshot; superseded by the separate final corrected source record.'
    record = {'source': str(original), 'whole': ident(final), 'cuts': [],
              'read_scope': 'WHOLE corrected final note reread.' if full_read else 'Final corrected metadata checked against exact current sources.'}
    if full_read:
        cut = own / 'cuts' / ('notes-current-prepared-recursive.md.' + sha(new)[:12] + '.L1-L201.txt')
        assert len(new.splitlines()) == 201
        cut.write_bytes(new)
        record['cuts'] = [{**ident(cut), 'first_line': 1, 'last_line': 201}]
    index['sources'].append(record)
    delta = own / 'documents' / (original.name + '.correction.diff')
    delta.write_text(''.join(difflib.unified_diff(old.decode().splitlines(True), new.decode().splitlines(True), fromfile='pre-correction', tofile='final-corrected')))
    corrections.append({'original_source': str(original), 'historical': ident(historical),
                        'final': ident(final), 'delta': ident(delta)})

note = (repo / 'lean/notes-current-prepared-recursive.md').read_bytes()
assert len(note) == 12698 and sha(note) == '6a75e8140387b6190948e1455726814b864589cde6323bccdb0d395518d93ce6'
for row in json.loads((area / 'document-validation.json').read_text()):
    data = (repo / row['path']).read_bytes()
    assert len(data) == row['bytes'] and sha(data) == row['sha256']
for row in index['sources']:
    data = Path(row['source']).read_bytes()
    assert data == Path(row['whole']['path']).read_bytes()
    assert len(data) == row['whole']['bytes'] and sha(data) == row['whole']['sha256']
    for cut in row['cuts']:
        part = b''.join(data.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']])
        assert part == Path(cut['path']).read_bytes()
        assert len(part) == cut['bytes'] and sha(part) == cut['sha256']
(own / 'source-index.json').write_text(json.dumps(index, indent=2) + '\n')
(own / 'documents/correction-review.json').write_text(json.dumps({
    'status': 'clear', 'reason': 'The old decoded value need not be ordinary. The final text correctly distinguishes the original stored handle from the current prepared ordinary parent.',
    'source_public_and_nine_insertions_changed': False,
    'revisions': corrections}, indent=2) + '\n')
verification = json.loads((own / 'verification-final.json').read_text())
verification['source_records'] = len(index['sources'])
verification['literal_line_cuts'] = sum(len(row['cuts']) for row in index['sources'])
verification['final_note_bytes'] = len(note)
verification['final_note_sha256'] = sha(note)
verification['state'] = 'CLEAR; ready for final report and exact-set seal'
(own / 'verification-final.json').write_text(json.dumps(verification, indent=2) + '\n')
print(json.dumps(verification))
