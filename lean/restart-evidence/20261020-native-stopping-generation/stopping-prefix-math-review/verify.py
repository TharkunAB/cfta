import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live-root', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    for item in manifest['files']:
        rel = Path(item['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        data = (HERE / rel).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['path']
    pins = json.loads((HERE / 'source-pins.json').read_text())
    for item in pins['root_sources']:
        data = (HERE / item['snapshot']).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256']
        if args.live_root:
            assert data == (args.root / item['path']).read_bytes(), item['path']
    for item in pins['candidates']:
        assert sha((HERE / item['snapshot']).read_bytes()) == item['sha256']
    checked = [item for item in pins['candidates'] if item['checked']]
    assert len(checked) == 2 and len(pins['candidates']) == 3
    assert (HERE / 'inputs/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
    groups = [
        ('stopping-site-direct-2', 'stopping-site-public-1', 'SourceCurrentNativeMuStoppingSite.lean',
         'MicroCFTA.SourceCurrentNativeMuStoppingSite.execute'),
        ('trace-bind-direct-1', 'trace-bind-public-1', 'SourceCurrentNativeTracePrefixBind.lean',
         'MicroCFTA.SourceCurrentNativeTracePrefixBind.bind_prefix_cases'),
    ]
    for strict, public, candidate, name in groups:
        source = (HERE / 'candidates' / candidate).read_bytes()
        for stem in [strict, public]:
            meta = json.loads((HERE / 'receipts' / (stem + '.json')).read_text())
            assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
            assert 'leanprover--lean4---v4.34.1/bin/lean' in meta['command'][0]
            assert sha((HERE / 'receipts' / meta['source']).read_bytes()) == meta['sha256']
            assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
            assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
            assert json.loads((HERE / 'receipts' / meta['limits']).read_text()) == {
                'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
            usage = json.loads((HERE / 'receipts' / (stem + '.usage.json')).read_text())
            assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert source == (HERE / 'receipts' / (strict + '.source.lean')).read_bytes()
        assert not (HERE / 'receipts' / (strict + '.log')).read_bytes()
        printer = (HERE / 'receipts' / (public + '.source.lean')).read_text()
        assert printer.encode().startswith(source)
        for option in OPTIONS:
            assert 'set_option ' + option in printer
        for command in ['#check @', '#print ', '#print axioms ']:
            assert command + name in printer
        for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
            assert len(re.findall(pattern, printer, re.M)) == 1
        log = (HERE / 'receipts' / (public + '.log')).read_text()
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
        assert len(reports) == 1
        for report in reports:
            cleaned = re.sub(r'\.\{[^}]*\}', '', report)
            assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    site = (HERE / 'candidates/SourceCurrentNativeMuStoppingSite.lean').read_text()
    prefix = (HERE / 'candidates/SourceCurrentNativeTracePrefixBind.lean').read_text()
    draft = (HERE / 'candidates/SourceCurrentNativeMuStoppingGeneration.lean').read_text()
    assert len(site.splitlines()) == 307 and len(draft.splitlines()) == 87
    assert 'SourceEqualityNativeDemand.execute count control before = resume remainingFuel siteStep' in site
    assert '(∀ value, inner ≠ .code (.pure value))' in prefix
    assert 'Trace outerFuel (.code (next value)) middle remaining after' in prefix
    status = json.loads((HERE / 'candidates/stopping-generation-draft-status.json').read_text())
    assert status['status'] == 'DRAFT_NOT_COMPILED' and status['lean_jobs'] == status['checked_public_heads'] == 0
    assert sha(draft.encode()) == status['source']['sha256']
    assert pins['counts'] == {'new_lean_jobs': 0, 'new_proof_pairs': 0,
                              'reused_checked_public_pairs': 2, 'unchecked_draft_heads': 1}
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), 'live_root': args.live_root,
                      'root_foundations': len(pins['root_sources']), 'candidate_snapshots': 3,
                      'new_lean_jobs': 0, 'new_proof_pairs': 0,
                      'reused_checked_public_pairs': 2, 'unchecked_draft_heads': 1}))


if __name__ == '__main__':
    main()
