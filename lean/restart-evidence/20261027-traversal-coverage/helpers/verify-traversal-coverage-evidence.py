from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('snapshot', type=Path)
parser.add_argument('--repository', type=Path, default=Path('/home/tritlo/Code/mcfta'))
parser.add_argument('--committed', action='store_true')
parser.add_argument('--live', action='store_true')
args = parser.parse_args()
snapshot = args.snapshot.resolve()
repository = args.repository.resolve()
old_area = Path('/tmp/mcfta-traversal-coverage-20261027')
old_repository = Path('/home/tritlo/Code/mcfta')


def digest(data):
    return hashlib.sha256(data).hexdigest()


actual = {str(p.relative_to(snapshot)) for p in snapshot.rglob('*') if p.is_file()}
if args.live:
    assert not args.committed
    manifest = {'files': [dict(path=name, bytes=len((snapshot/name).read_bytes()),
        sha256=digest((snapshot/name).read_bytes())) for name in sorted(actual)]}
    decoded = []
else:
    manifest = json.loads((snapshot / 'manifest.json').read_text())
    decoded = json.loads((snapshot / 'decoded-files.json').read_text())
expected = {record['path'] for record in manifest['files']}
assert actual == expected | (set() if args.live else {'manifest.json'})
for record in manifest['files']:
    path = snapshot / record['path']
    assert not path.is_symlink()
    data = path.read_bytes()
    assert len(data) == record['bytes'] and digest(data) == record['sha256'], path
archives = {item['original_path']: item for item in decoded}


def read(relative):
    path = snapshot / relative
    if path.is_file():
        return path.read_bytes()
    record = archives[str(relative)]
    data = gzip.decompress((snapshot / record['stored_path']).read_bytes())
    assert len(data) == record['bytes'] and digest(data) == record['sha256'], relative
    return data


for name in archives:
    read(name)


def relocated(path, review):
    path = Path(path)
    if path.is_absolute() and path.is_relative_to(old_area):
        return read(path.relative_to(old_area))
    if path.is_absolute() and path.is_relative_to(old_repository):
        return (repository / path.relative_to(old_repository)).read_bytes()
    if path == Path('/tmp/mcfta-document-traversal-coverage.py'):
        return path.read_bytes() if args.live else read('helpers/document-traversal-coverage.py')
    if path.is_absolute():
        raise ValueError(path)
    return read(review / path)


def original_of(entry):
    name = entry.get('source', entry.get('source_path', entry.get('path')))
    path = Path(name)
    return str(path if path.is_absolute() else old_repository / path)


def first_of(entry):
    return entry.get('first_line', entry.get('first', entry.get('start', entry.get('start_line'))))


review_records = 0
historical_sources = []
for name in sorted(actual | set(archives)):
    source_index = name.endswith('/source-index.json')
    source_pins = Path(name).name in {
        'source-pins.json', 'draft-pins.json', 'source-pins-final.json',
        'root-review-source-pins-open.json', 'public-focused-pins.json',
        'document-source-pins.json', 'public-source-pins.json'}
    if not source_index and not (source_pins and len(Path(name).parts) == 2):
        continue
    review = Path(name).parent
    entries = []

    def visit(value, inherited_source=None, inherited_hash=None):
        if isinstance(value, list):
            for item in value:
                visit(item, inherited_source, inherited_hash)
        elif isinstance(value, dict):
            copied = value.get('snapshot', value.get('copy_path'))
            original = value.get('source', value.get('source_path', value.get('path', inherited_source)))
            source_hash = inherited_hash
            if original and 'sha256' in value and first_of(value) is None and 'byte_start' not in value:
                source_hash = value['sha256']
            if copied and original and 'sha256' in value:
                entry = dict(value, source=original)
                if first_of(entry) is not None and 'source_sha256' not in entry:
                    entry['source_sha256'] = inherited_hash
                entries.append(entry)
                if first_of(entry) is None and 'byte_start' not in entry:
                    source_hash = entry['sha256']
            for item in value.values():
                visit(item, original, source_hash)

    parsed = json.loads(read(name))
    if source_index and isinstance(parsed, dict) and 'sources' in parsed and all('whole' in source for source in parsed['sources']):
        for source in parsed['sources']:
            original = source['source']
            whole = source['whole']
            entries.append(dict(whole, source=original, snapshot=whole['path']))
            for cut in source.get('cuts', [source['cut']] if 'cut' in source else []):
                entries.append(dict(cut, source=original, snapshot=cut['path'], source_sha256=whole['sha256']))
    elif source_index and isinstance(parsed, dict) and 'sources' in parsed and all('whole_path' in source for source in parsed['sources']):
        for source in parsed['sources']:
            original = source['source_path']
            entries.append(dict(source=original, snapshot=source['whole_path'],
                bytes=source['whole_bytes'], sha256=source['whole_sha256']))
            for cut in source.get('cuts', []):
                entries.append(dict(cut, source=original, snapshot=cut['path'],
                    source_sha256=source['whole_sha256']))
    elif source_index and isinstance(parsed, dict) and 'sources' in parsed and all('whole_copy' in source for source in parsed['sources']):
        for source in parsed['sources']:
            original = source['source']
            entries.append(dict(source=original, snapshot=source['whole_copy'],
                bytes=source['whole_bytes'], sha256=source['whole_sha256']))
            for cut in source.get('inspected_literal_cuts', []):
                entries.append(dict(source=original, snapshot=cut['copy'],
                    bytes=cut['bytes'], sha256=cut['sha256'],
                    first_line=cut['start_line'], last_line=cut['end_line'],
                    source_sha256=source['whole_sha256']))
    elif source_index and isinstance(parsed, dict) and 'sources' in parsed and all('copy' in source for source in parsed['sources']):
        for source in parsed['sources']:
            original = source.get('source', source.get('source_path'))
            assert original, (name, source)
            entries.append(dict(source, source=original, snapshot=source['copy']))
            for cut in source.get('cuts', []):
                copied = cut.get('copy', cut.get('path', cut.get('snapshot')))
                assert copied, (name, cut)
                entries.append(dict(cut, source=original, snapshot=copied,
                    source_sha256=source['sha256']))
        for cut in parsed.get('cuts', []):
            entries.append(dict(cut, snapshot=cut['copy'], source_sha256=cut['whole_sha256']))
    elif isinstance(parsed, dict) and parsed.get('sources') and all('copy' in source for source in parsed['sources']):
        for source in parsed['sources']:
            original = source.get('source', source.get('source_path'))
            entries.append(dict(source, source=original, snapshot=source['copy']))
            for cut in source.get('cuts', []):
                entries.append(dict(cut, source=original, snapshot=cut.get('copy', cut.get('path')),
                    source_sha256=source['sha256']))
        for cut in parsed.get('cuts', []):
            entries.append(dict(cut, snapshot=cut.get('copy', cut.get('path'))))
    else:
        visit(parsed)
    assert entries, ('No recognized source pins', name)
    wholes = {}
    for entry in entries:
        copied = entry.get('snapshot', entry.get('copy_path'))
        original = original_of(entry)
        data = relocated(copied, review)
        assert len(data) == entry['bytes'] and digest(data) == entry['sha256'], (name, copied)
        first = first_of(entry)
        if first is None and 'byte_start' not in entry:
            wholes[(original, digest(data))] = data
    for entry in entries:
        copied = entry.get('snapshot', entry.get('copy_path'))
        original = original_of(entry)
        data = relocated(copied, review)
        first = first_of(entry)
        last = entry.get('last_line', entry.get('last', entry.get('end', entry.get('end_line'))))
        if 'byte_start' in entry:
            full = relocated(original, review)
            assert len(full) == entry['source_bytes'] and digest(full) == entry['source_sha256'], (name, original)
            assert full[entry['byte_start']:entry['byte_end_exclusive']] == data, (name, copied)
        elif first is not None:
            full_hash = entry.get('source_sha256')
            candidates = [value for (source, sha), value in wholes.items()
                          if source == original and (full_hash is None or full_hash == sha)]
            if not candidates:
                candidates = [relocated(original, review)]
                if full_hash is not None:
                    assert digest(candidates[0]) == full_hash, (name, original)
            assert any(b''.join(full.splitlines(keepends=True)[first-1:last]) == data
                       for full in candidates), (name, copied)
        else:
            live = relocated(original, review)
            if live != data:
                historical_sources.append({'review': name, 'source': original,
                                           'historical_sha256': digest(data), 'current_sha256': digest(live)})
        review_records += 1

review_seals = 0
supplements = json.loads(read('seal-supplements.json'))['reviews']
used_supplements = set()
logical_files = (actual - {record['stored_path'] for record in decoded}) | set(archives)
for name in sorted(logical_files):
    if not name.endswith('/pins.json') or len(Path(name).parts) != 2:
        continue
    review = Path(name).parent
    pins = json.loads(read(name))
    payloads = pins.get('payloads', pins.get('pins', pins.get('files')))
    if payloads is None and all(isinstance(record, dict) and 'sha256' in record for record in pins.values()):
        payloads = pins
    if isinstance(payloads, dict):
        payloads = [dict(record, path=path) for path, record in payloads.items()]
    assert isinstance(payloads, list), name
    if 'payload_count' in pins:
        assert len(payloads) == pins['payload_count']
        pins_count = pins.get('file_count_including_pins', pins.get('exact_file_count_including_pins'))
        if pins_count is not None:
            assert len(payloads) + 1 == pins_count
    if 'count' in pins:
        assert len(payloads) == pins['count']
    expected_review = {str(review / record['path']) for record in payloads} | {name}
    frozen_name = str(review / 'FROZEN.json')
    if frozen_name not in logical_files and str(review / 'FROZEN') in logical_files:
        frozen_name = str(review / 'FROZEN')
    if frozen_name in logical_files:
        seal = json.loads(read(frozen_name))
        pin_seal = seal.get('pins', {})
        if isinstance(pin_seal, str):
            assert pin_seal == 'pins.json'
            pin_seal = {}
        assert isinstance(pin_seal, dict)
        if 'manifest_sha256' in seal:
            assert seal['manifest'] == 'pins.json'
        assert digest(read(name)) == seal.get('pins_sha256', seal.get('manifest_sha256', pin_seal.get('sha256')))
        sealed_pin_bytes = seal.get('pins_bytes', seal.get('manifest_bytes', pin_seal.get('bytes')))
        if sealed_pin_bytes is not None:
            assert len(read(name)) == sealed_pin_bytes
        assert len(payloads) == seal.get('payload_count', seal.get('payload_files', seal.get('pins_count', seal.get('payloads'))))
        expected_review.add(frozen_name)
        exact_count = seal.get('exact_file_count', seal.get('file_count', seal.get('exact_physical_files', seal.get('exact_files', seal.get('physical_files_including_manifest_and_seal')))))
        if exact_count is not None:
            assert len(expected_review) == exact_count
    if str(review) in supplements:
        supplement = supplements[str(review)]
        for field, path in [('pins', name), ('seal', frozen_name)]:
            data = read(path)
            assert len(data) == supplement[field]['bytes'] and digest(data) == supplement[field]['sha256']
        assert len(expected_review) == supplement['declared_file_count']
        for record in supplement['files']:
            path = str(review / record['path'])
            assert path not in expected_review
            data = read(path)
            assert len(data) == record['bytes'] and digest(data) == record['sha256']
            assert data == read(record['original_path'])
            expected_review.add(path)
        assert len(expected_review) == supplement['actual_file_count']
        used_supplements.add(str(review))
    actual_review = {path for path in logical_files if Path(path).is_relative_to(review)}
    assert expected_review == actual_review, (name, expected_review ^ actual_review)
    for record in payloads:
        data = read(review / record['path'])
        assert len(data) == record['bytes'] and digest(data) == record['sha256'], (name, record['path'])
    review_seals += 1
assert used_supplements == set(supplements)

for module in json.loads(read('modules.json')) + ['Audit'] + [record['module'] for record in json.loads(read('prior-strong-sources.json'))]:
    relative = Path('lean/MicroCFTA') / (module + '.lean')
    assert read(Path('installed-sources') / relative) == (repository / relative).read_bytes()
for status in json.loads(read('document-validation.json')):
    current = (repository / status['path']).read_bytes()
    assert len(current) == status['bytes'] and digest(current) == status['sha256']
    if status.get('inserted_bytes') is not None:
        old = read(Path('prior-documents') / status['path'])
        offset = status['offset']
        count = status['inserted_bytes']
        assert current[:offset] + current[offset+count:] == old
if args.committed:
    prefix = snapshot.relative_to(repository)
    tracked = subprocess.check_output(['git', 'ls-files', '-z', '--', str(prefix)], cwd=repository)
    names = {str(Path(item.decode()).relative_to(prefix)) for item in tracked.split(b'\0') if item}
    assert names == actual
    for name in names:
        data = subprocess.check_output(['git', 'show', 'HEAD:' + str(prefix / name)], cwd=repository)
        assert data == (snapshot / name).read_bytes(), name
print(json.dumps({'status': 'pass', 'payloads': len(expected),
    'bytes': sum(r['bytes'] for r in manifest['files']), 'archives': len(archives),
    'review_records': review_records, 'review_seals': review_seals, 'supplemented_reviews': sorted(used_supplements), 'historical_sources': historical_sources,
    'committed': args.committed, 'manifest_sha256': None if args.live else digest((snapshot / 'manifest.json').read_bytes())}))
