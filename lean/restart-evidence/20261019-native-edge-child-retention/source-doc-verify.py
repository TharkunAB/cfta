import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify_files(path):
    entries = json.loads(path.read_text())['files']
    for item in entries:
        data = (ROOT / item['path']).read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert digest(data) == item['sha256'], item['path']
    return len(entries)


def main():
    count = verify_files(HERE / 'source-doc-pins.json')
    source_count = verify_files(HERE / 'progress-review-source-pins.json')
    ranges = json.loads((HERE / 'source-doc-ranges.json').read_text())['ranges']
    assert len(ranges) == 12
    for item in ranges:
        assert digest(item['text'].encode()) == item['sha256'], item['path']
        if '--live' in sys.argv:
            lines = (ROOT / item['path']).read_text().splitlines(keepends=True)
            actual = ''.join(lines[item['start_line'] - 1:item['end_line']])
            assert actual == item['text'], item['path']
    audit = json.loads((HERE / 'full-audit-1.json').read_text())
    assert audit['exit_code'] == 0
    log = (HERE / audit['log']).read_text()
    assert 'Build completed successfully (3462 jobs).' in log
    assert 'Checked axiom dependencies of 73854 MicroCFTA theorems.' in log
    print(json.dumps({'status': 'PASS', 'pins': count, 'source_review_pins': source_count,
                      'reviewed_ranges': 12, 'live_ranges_checked': '--live' in sys.argv,
                      'new_lean_runs': 0, 'new_proof_pairs': 0,
                      'reused_public_pairs': 8, 'reused_constructed_pairs': 1}))


if __name__ == '__main__':
    main()
