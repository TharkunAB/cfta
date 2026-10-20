"""Check the one-pin canonical-warning correction and final live readback."""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
EVIDENCE = Path('lean/restart-evidence/20261020-native-optional-owner-prefix')
OLD_SHA = '1fbc876245a89dbf12315652123e44a84948f89301218ad8df036b4e5e2965a3'
NEW_SHA = '1c0fc50717df686b3b7b9aeafda30158f1a0b2090d4dd5ed46d3548e2d798b90'
WARNING = 'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'


def read(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    args = parser.parse_args()
    manifest = read(HERE / 'amendment-manifest.json')
    for base, entries in [(args.root, manifest['sources']), (HERE, manifest['files'])]:
        for item in entries:
            path = Path(item['path'])
            assert not path.is_absolute() and '..' not in path.parts
            data = (base / path).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    evidence = args.root / EVIDENCE
    before = evidence / 'source-doc-before-canonical-warning-source-pins.json'
    after = evidence / 'source-doc-source-pins.json'
    assert hashlib.sha256(before.read_bytes()).hexdigest() == OLD_SHA
    assert hashlib.sha256(after.read_bytes()).hexdigest() == NEW_SHA
    old, new = read(before), read(after)
    assert old.keys() == new.keys()
    for key in old:
        if key != 'files':
            assert old[key] == new[key], key
    old_files = {item['path']: item for item in old['files']}
    new_files = {item['path']: item for item in new['files']}
    assert old_files.keys() == new_files.keys()
    changed = [key for key in old_files if old_files[key] != new_files[key]]
    assert changed == [str(EVIDENCE / 'selected-canonical-warnings.json')]
    canonical = read(evidence / 'selected-canonical.json')
    mapping = read(evidence / 'selected-canonical-warnings.json')
    assert len(canonical) == 9 and len(set(canonical.values())) == 8
    assert mapping == {name: [WARNING] for name in canonical}
    for stem in set(canonical.values()):
        assert re.findall(r'^warning:.*$', (evidence / (stem + '.log')).read_text(), re.M) == [WARNING], stem
    readback = read(HERE / 'refreshed-source-doc-live-verification.json')
    assert readback['status'] == 'PASS' and readback['live']
    assert readback['ranges'] == 13 and readback['root_pins'] == 358
    assert readback['all_archived_lean_lake_commands'] == 62 and readback['all_archived_failures'] == 17
    assert readback['new_lean_jobs'] == readback['new_proof_pairs'] == 0
    assert not (HERE / 'refreshed-source-doc-live-verification.stderr.txt').read_bytes()
    print(json.dumps({'status': 'PASS', 'changed_source_pins': 1,
                      'canonical_module_mappings': 9, 'unique_canonical_logs': 8,
                      'source_doc_live_readback': 'PASS', 'new_lean_jobs': 0,
                      'new_proof_pairs': 0, 'pins': len(manifest['sources']) + len(manifest['files'])}))


if __name__ == '__main__':
    main()
