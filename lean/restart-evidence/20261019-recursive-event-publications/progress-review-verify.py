import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def checked_meta(stem: str) -> dict:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    wrapper = meta['wrapper']
    assert wrapper[wrapper.index('--mem') + 1] == '4G', stem
    assert wrapper[wrapper.index('--time') + 1] == '5m', stem
    if 'source' in meta:
        data = (HERE / meta['source']).read_bytes()
        assert hashlib.sha256(data).hexdigest() == meta['sha256'], stem
    return meta


def main() -> None:
    pins = json.loads((HERE / 'progress-review-source-pins.json').read_text())
    for item in pins['files']:
        path = ROOT / item['path']
        data = path.read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    selected = json.loads((HERE / 'progress-review-selection.json').read_text())
    checks = runpy.run_path(str(HERE / 'verify-probes.py'), run_name='progress_review_reuse')
    for group in selected['groups']:
        checked_meta(group['name'])
        checks['check_group'](group)
    for item in selected['strict']:
        stem = item['name']
        meta = checked_meta(stem)
        assert not (HERE / meta['log']).read_bytes(), stem
        assert (HERE / meta['source']).read_bytes() == (ROOT / item['source']).read_bytes(), stem
        checks['check_limits'](stem)
    for stem in selected['canonical']:
        meta = checked_meta(stem)
        checks['check_limits'](stem)
        log = (HERE / meta['log']).read_text()
        assert 'error:' not in log and 'sorryAx' not in log, stem
        warnings = [line for line in log.splitlines() if line.startswith('warning:')]
        assert all('InternedFreshOrdinaryClosedCompletion.lean:24:5:' in line for line in warnings), stem
    print(json.dumps({'status': 'PASS', 'pins': len(pins['files']), 'counts': selected['counts']}, indent=2))


if __name__ == '__main__':
    main()
