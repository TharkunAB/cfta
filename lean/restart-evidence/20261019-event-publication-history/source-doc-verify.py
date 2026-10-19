import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    pins = json.loads((HERE / 'source-doc-pins.json').read_text())['files']
    for item in pins:
        data = (ROOT / item['path']).read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    ranges = json.loads((HERE / 'source-doc-ranges.json').read_text())['ranges']
    for item in ranges:
        assert hashlib.sha256(item['text'].encode()).hexdigest() == item['sha256'], item['path']
        assert len(item['text'].splitlines()) == item['end_line'] - item['start_line'] + 1
        if args.live:
            lines = (ROOT / item['path']).read_text().splitlines(keepends=True)
            actual = ''.join(lines[item['start_line'] - 1:item['end_line']])
            assert actual == item['text'], item['path']
    assert len({item['text'] for item in ranges[:7]}) == 1
    selection = json.loads((HERE / 'source-doc-selection.json').read_text())
    spec = importlib.util.spec_from_file_location('doc_probe_tools', HERE / 'merge-probe-tools.py')
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    for stem in selection['strict']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0, stem
        assert not (HERE / meta['log']).read_bytes(), stem
        probe.check_limits(stem)
    for stem in selection['canonical']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        log = (HERE / meta['log']).read_text()
        assert meta['exit_code'] == 0, stem
        assert 'Build completed successfully' in log, stem
        assert not re.search(r'(^|\n)error:', log), stem
        probe.check_limits(stem)
    for group in selection['groups']:
        probe.check_group(group)
    audit = json.loads((HERE / 'full-audit-1.json').read_text())
    audit_log = (HERE / audit['log']).read_text()
    assert audit['exit_code'] == 0
    assert 'Build completed successfully (3468 jobs).' in audit_log
    assert 'Checked axiom dependencies of 73931 MicroCFTA theorems.' in audit_log
    probe.check_limits('full-audit-1')
    preservation = json.loads((HERE / 'preservation-final.json').read_text())
    assert preservation['status'] == 'PASS'
    assert preservation['all_starting_haskell_files'] == 268
    assert preservation['all_haskell_unchanged']
    assert preservation['active_package_files'] == 207
    assert preservation['all_active_package_files_unchanged']
    print(json.dumps({'status': 'PASS', 'live': args.live, 'ranges': len(ranges),
                      'pins': len(pins), 'reused_public_pairs': 30,
                      'reused_constructed_pairs': 1, 'new_lean_jobs': 0,
                      'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
