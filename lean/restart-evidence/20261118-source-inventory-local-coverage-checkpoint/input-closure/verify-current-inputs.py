from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
ARCHIVE = BASE / '20261118-source-inventory-local-coverage-checkpoint'
CONTROL = BASE / '20261118-source-inventory-local-coverage-checkpoint-control-draft'
CODE = 'a789d75bf0ac472447d09547e380c30904225509'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
exact, by_digest, checked_payloads = {}, {}, set()


def add(original, digest, payload, compressed, classification, encoded_digest=None):
    entry = {'payload': str(payload.relative_to(ROOT)), 'gzip': compressed,
             'classification': classification, 'encoded_sha256': encoded_digest}
    exact.setdefault((original, digest), entry)
    by_digest.setdefault(digest, entry)


def index_archive(path, expected_manifest=None, expected_records=None):
    manifest_path = path / 'manifest.json'
    manifest = None
    if expected_manifest is not None:
        assert SHA(manifest_path.read_bytes()) == expected_manifest
        manifest = read(manifest_path)
    encoded = {item['path']: item['sha256'] for item in manifest['files']} if manifest else {}
    records_path = path / 'archived-inputs.json'
    if expected_records is not None:
        assert SHA(records_path.read_bytes()) == expected_records
    if manifest:
        assert SHA(records_path.read_bytes()) == encoded['archived-inputs.json']
    for item in read(records_path):
        original = str(Path(item['original']).relative_to(ROOT))
        add(original, item['source_sha256'], path / item['archived'], item['gzip'],
            'selected_original' if path == ARCHIVE else 'ancestor_original',
            encoded.get(item['archived']))
    if manifest:
        for item in manifest['files']:
            payload = path / item['path']
            add(str(payload.relative_to(ROOT)), item['sha256'], payload, False,
                'ancestor_metadata', item['sha256'])
        add(str(manifest_path.relative_to(ROOT)), expected_manifest, manifest_path,
            False, 'ancestor_metadata', expected_manifest)


index_archive(ARCHIVE)
ancestors = read(CONTROL / 'ARCHIVE-PIN-COVERAGE-OPEN.json')['linked_ancestor_archives']
assert len(ancestors) == 49
for ancestor in ancestors:
    index_archive(BASE / ancestor['root'], ancestor['manifest_sha256'],
                  ancestor['archived_inputs_sha256'])

maps = [
    BASE / '20261118-source-inventory-local-coverage-publication/source-pins.json',
    BASE / '20261118-source-inventory-local-coverage-repair-check/source-pins.json',
    BASE / '20261118-source-inventory-local-coverage-check/source-pins.json',
    BASE / '20261118-query-coverage-relations-done-assignment-publication/source-pins.json',
    CONTROL / 'SOURCE-PINS.json',
]
normal = read(BASE / '20261118-source-inventory-local-coverage-work/NORMAL-SOURCE-PINS.json')
assert len(normal) == 6294
resolutions, counts, map_counts = {}, Counter(), {}
for pinmap in maps:
    pins = read(pinmap)
    map_counts[str(pinmap.relative_to(ROOT))] = len(pins)
    for name, digest in pins.items():
        key = (name, digest)
        if key in resolutions:
            continue
        if normal.get(name) == digest:
            assert SHA((ROOT / name).read_bytes()) == digest, name
            entry = {'classification': 'checked_source_or_toolchain',
                     'source_commit': CODE, 'payload': name, 'gzip': False}
        else:
            entry = exact.get(key) or by_digest.get(digest)
            assert entry is not None, ('No archived recovery', name, digest)
            entry = dict(entry)
            if key not in exact:
                entry['classification'] = 'archived_exact_copy'
            payload = ROOT / entry['payload']
            payload_key = (entry['payload'], entry['gzip'], digest)
            if payload_key not in checked_payloads:
                data = payload.read_bytes()
                if entry['encoded_sha256'] is not None:
                    assert SHA(data) == entry['encoded_sha256'], payload
                if entry['gzip']:
                    data = gzip.decompress(data)
                assert SHA(data) == digest, (name, payload)
                checked_payloads.add(payload_key)
        resolutions[key] = entry
        counts[entry['classification']] += 1
print(json.dumps({
    'status': 'FINAL ROOT ACTUAL INPUT RECOVERY VERIFIED',
    'source_commit': CODE, 'publication_actual_session': 17653,
    'publication_input_pins': map_counts[str(maps[0].relative_to(ROOT))],
    'all_five_input_maps_recoverable': True,
    'input_map_counts': map_counts, 'distinct_path_digest_pairs': len(resolutions),
    'recovery_classifications': dict(counts),
    'linked_ancestor_archives': len(ancestors),
    'ancestor_archives_recursively_copied': False,
    'normal_source_toolchain_hashes_verified': len(normal),
    'unique_archived_payloads_rehashed_and_decompressed': len(checked_payloads),
    'selected_archived_inputs': len(read(ARCHIVE / 'archived-inputs.json')),
    'generated_or_unclassified_extra_authored_credit': 0,
    'joint_finite_completion_proved': False,
}, indent=2))
