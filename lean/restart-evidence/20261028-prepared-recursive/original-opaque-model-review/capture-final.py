from pathlib import Path
import hashlib
import json
import shutil

REPO = Path('/home/tritlo/Code/mcfta')
AREA = Path('/tmp/mcfta-prepared-recursive-20261028')
OWN = AREA / 'original-opaque-model-review'
assert not (OWN / 'FROZEN.json').exists()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha(data)}


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def copy(source, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    data = source.read_bytes()
    if destination.exists():
        assert destination.read_bytes() == data, destination
    else:
        destination.write_bytes(data)
    return destination


index = json.loads((OWN / 'source-index.json').read_text())


def pin(source, spans, scope, destination=None):
    data = source.read_bytes()
    tag = source.name + '.' + sha(data)[:12]
    destination = destination or OWN / 'sources' / (tag + '.whole')
    copy(source, destination)
    record = {'source': str(source), 'whole': identity(destination),
              'cuts': [], 'read_scope': scope}
    lines = data.splitlines(keepends=True)
    for first, last in spans:
        assert 1 <= first <= last <= len(lines)
        path = OWN / 'cuts' / (tag + f'.L{first}-L{last}.txt')
        selected = b''.join(lines[first - 1:last])
        if path.exists():
            assert path.read_bytes() == selected
        else:
            path.write_bytes(selected)
        record['cuts'].append({**identity(path), 'first_line': first,
                               'last_line': last})
    index['sources'].append(record)
    return destination


metadata = [
    'source-head.txt', 'source-commits.json', 'published-base.txt',
    'source-validation.json', 'public-validation.json',
    'preservation-validation.json', 'root-contract-comparisons.json',
    'actual-commands.json', 'modules.json', 'strict-checks.json',
    'new-public-declarations.json', 'public-declarations.json',
    'public-definitions.json', 'audit-import-insertion.json',
    'document-paths.json', 'document-validation.json',
]
for name in metadata:
    source = AREA / name
    pin(source, [], 'Final evidence metadata inspected; copied whole for exact identity.',
        OWN / 'evidence' / 'final' / name)

commands = json.loads((AREA / 'actual-commands.json').read_text())
assert len(commands) == 26
assert sum(x['report']['exit_code'] != 0 for x in commands) == 4
checked_commands = []
for row in commands:
    name, report = row['name'], row['report']
    original = AREA / name
    local = OWN / 'evidence' / name
    raw = (original / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    assert report['cgroup_limits'] == {
        'memory.max': '4294967296', 'memory.high': '4294967296',
        'memory.swap.max': '0'}
    copy(original / 'report.json', local / 'report.json')
    copy(original / 'raw.log', local / 'raw.log')
    snapshots = []
    for source in sorted(original.rglob('*.lean')):
        target = copy(source, local / source.relative_to(original))
        snapshots.append(identity(target))
    if report.get('source_sha256'):
        assert any(x['sha256'] == report['source_sha256'] for x in snapshots), name
    checked_commands.append({'name': name, 'exit_code': report['exit_code'],
                             'raw': identity(local / 'raw.log'),
                             'snapshots': snapshots})
write_json(OWN / 'evidence' / 'command-checks.json', checked_commands)

validation = json.loads((AREA / 'source-validation.json').read_text())
for entry in validation['strict_checks']:
    source = REPO / 'lean' / 'MicroCFTA' / (entry['module'] + '.lean')
    data = source.read_bytes()
    assert len(data) == entry['bytes'] and sha(data) == entry['sha256']
    scope = ('Final source identity and complete public conclusion reviewed. '
             'Other owners review this module proof; no claim of independent whole-proof review here.')
    if entry['module'] in {
        'SourcePruningEnumerationReceiptContinuation',
        'SourcePruningEnumerationSelectedContinuations',
        'SourcePruningEnumerationSelectedOpaquePreparationModels',
        'SourcePruningEnumerationSelectedOpaqueHookModels',
    }:
        scope = 'Whole actual source and proof reviewed, including all final immutable deltas.'
    pin(source, [], scope)

public = (AREA / 'public-readback-final' / 'raw.log').read_bytes()
prior = (AREA / 'prior-public-readback' / 'raw.log').read_bytes()
appendix = (AREA / 'new-public-blocks.txt').read_bytes()
pv = json.loads((AREA / 'public-validation.json').read_text())
assert len(prior) == 1442414
assert public == prior + appendix
assert len(public) == pv['bytes'] and sha(public) == pv['sha256']
assert len(appendix) == pv['new_bytes'] and sha(appendix) == pv['new_sha256']
pin(AREA / 'new-public-blocks.txt', [(1, len(appendix.splitlines()))],
    'WHOLE final 1935-line appendix read in untruncated ranges; all 21 new full signatures/axioms and nine printed definitions reviewed.',
    OWN / 'evidence' / 'final' / 'new-public-blocks.txt')
copy(AREA / 'prior-public-readback' / 'raw.log',
     OWN / 'evidence' / 'prior-public-readback' / 'raw.log')
write_json(OWN / 'evidence' / 'public-prefix-check.json', {
    'status': 'pass', 'prior': identity(OWN / 'evidence' / 'prior-public-readback' / 'raw.log'),
    'current': identity(OWN / 'evidence' / 'public-readback-final' / 'raw.log'),
    'appendix': identity(OWN / 'evidence' / 'final' / 'new-public-blocks.txt'),
    'relation': 'current = prior ++ appendix; exact bytes',
    'semantic_read_scope': 'Entire new appendix; historical prefix checked by bytes, not reread.'})

compared = []
for number, row in enumerate(json.loads((AREA / 'root-contract-comparisons.json').read_text())['comparisons'], 1):
    left, right = AREA / row['original'], AREA / row['recovered']
    data = left.read_bytes()
    assert data == right.read_bytes()
    assert len(data) == row['bytes'] and sha(data) == row['sha256']
    a = copy(left, OWN / 'evidence' / 'contract-recoveries' / f'{number}-original.txt')
    b = copy(right, OWN / 'evidence' / 'contract-recoveries' / f'{number}-recovered.txt')
    compared.append({'original_source': str(left), 'recovered_source': str(right),
                     'original': identity(a), 'recovered': identity(b),
                     'status': 'byte-identical',
                     'scope': 'Explicit declaration text. Namespace, changed admission and type binding differences remain explicit.'})
write_json(OWN / 'evidence' / 'contract-recovery-checks.json', compared)

documents = json.loads((AREA / 'document-validation.json').read_text())
inverses = []
for row in documents:
    source = REPO / row['path']
    data = source.read_bytes()
    assert len(data) == row['bytes'] and sha(data) == row['sha256']
    if 'inserted_bytes' not in row:
        pin(source, [(1, len(data.splitlines()))],
            'WHOLE final new note read; all strongest-claim, worker-type, pre-hook model, zero-expansion and physical Haskell limits reviewed.',
            OWN / 'documents' / row['path'])
        continue
    offset, count = row['offset'], row['inserted_bytes']
    inserted = data[offset:offset + count]
    old = data[:offset] + data[offset + count:]
    actual_prior = (AREA / 'prior-documents' / row['path']).read_bytes()
    assert old == actual_prior
    assert len(old) == row['prior_bytes'] and sha(old) == row['prior_sha256']
    first = len(data[:offset].splitlines()) + 1
    last = len(data[:offset + count].splitlines())
    # These inserted regions start and end on complete line boundaries.
    assert inserted == b''.join(data.splitlines(keepends=True)[first - 1:last])
    target = pin(source, [(first, last)],
                 'Semantic review covers ONLY the exact current inserted region. Whole current body is preserved for exact identity and inverse recovery; historical text was not reread.',
                 OWN / 'documents' / row['path'])
    insert_path = OWN / 'documents' / 'insertions' / (row['path'].replace('/', '__') + '.txt')
    insert_path.parent.mkdir(parents=True, exist_ok=True)
    insert_path.write_bytes(inserted)
    expected = (AREA / ('document-findings-insertion.txt' if row['path'] == 'FINDINGS.md' else 'document-common-insertion.txt')).read_bytes()
    assert inserted == expected
    inverses.append({'source': str(source), 'current': identity(target),
                     'insert': identity(insert_path), 'offset': offset,
                     'inserted_bytes': count, 'prior_bytes': len(old),
                     'prior_sha256': sha(old), 'prior_source': str(AREA / 'prior-documents' / row['path']),
                     'reconstruction': 'Remove current[offset:offset+inserted_bytes] to recover the exact prior bytes.'})
assert len(inverses) == 9
write_json(OWN / 'document-inverses.json', inverses)

for row in index['sources']:
    source, whole = Path(row['source']), row['whole']
    data = source.read_bytes()
    assert data == Path(whole['path']).read_bytes(), source
    assert len(data) == whole['bytes'] and sha(data) == whole['sha256']
    for cut in row['cuts']:
        selected = b''.join(data.splitlines(keepends=True)[cut['first_line'] - 1:cut['last_line']])
        assert selected == Path(cut['path']).read_bytes(), cut
        assert len(selected) == cut['bytes'] and sha(selected) == cut['sha256']
write_json(OWN / 'source-index.json', index)
write_json(OWN / 'verification-final.json', {
    'status': 'pass', 'source_records': len(index['sources']),
    'literal_line_cuts': sum(len(row['cuts']) for row in index['sources']),
    'exact_document_inverses': len(inverses), 'commands': len(commands),
    'failed_commands': 4, 'strict_final_passes': 12,
    'public_prefix_bytes': len(prior), 'public_bytes': len(public),
    'new_public_appendix_bytes': len(appendix),
    'all_source_wholes_and_literal_cuts_verified': True,
    'all_measured_limits': '4 GiB memory.max/high; zero swap',
    'owner_compiler_build_native_git_network_repo_writes': 0,
    'state': 'OPEN until report and exact-set seal are complete'})
print(json.dumps({'sources': len(index['sources']),
                  'cuts': sum(len(row['cuts']) for row in index['sources']),
                  'inverses': len(inverses), 'commands': len(commands)}))
