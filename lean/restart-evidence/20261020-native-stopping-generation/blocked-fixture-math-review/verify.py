import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


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
    for item in pins['sources']:
        data = (HERE / item['snapshot']).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256']
        if args.live_root:
            assert data == (args.root / item['path']).read_bytes(), item['path']
    source = (HERE / 'blocked-allocation-kernels.lean').read_bytes()
    assert sha(source) == pins['candidate']['sha256'] == '7dd73744d8e9e300dabfdc06367d95d98547f67605e69a44eb87d2fd83c3761d'
    assert (HERE / 'inputs/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
    for stem in ['blocked-allocation-direct-2', 'blocked-allocation-public-1']:
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
    assert source == (HERE / 'receipts/blocked-allocation-direct-2.source.lean').read_bytes()
    assert not (HERE / 'receipts/blocked-allocation-direct-2.log').read_bytes()
    printer = (HERE / 'receipts/blocked-allocation-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    name = 'MicroCFTA.NativeBlockedAllocationFixture.actual_blocked_nested_creation'
    for command in ['#check @', '#print ', '#print axioms ']:
        assert command + name in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    log = (HERE / 'receipts/blocked-allocation-public-1.log').read_text()
    assert len(log.encode()) == 382991
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    for report in reports:
        names = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    text = source.decode()
    assert text.count('rcases SourceCurrentNativeMuStoppingGeneration.execute ') == 1
    checked = text.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
    public = text.split('theorem actual_blocked_nested_creation :\n', 1)[1].split(' := checked_witness', 1)[0]
    assert checked == public
    for fact in ['actualDepth = .done (valueOf oracleDepth) actualDepth.state',
                 'actualOrdinary = .done (valueOf oracleOrdinary) actualOrdinary.state',
                 'warm.nodeRecords targetKey = none', 'bound.state.nodeRecords targetKey = some target',
                 'InternedFreshOrdinaryDepthHeap.usesLocal targetDepth targetOrdinary = true',
                 'outcome = .blocked (.native (.constructor outerKey)) (.code binder) after',
                 'rw [target_missing] at prior']:
        assert fact in text
    owner = json.loads((HERE / 'blocked-allocation-selection.json').read_text())
    assert owner['finalized'] and owner['lean_jobs'] == 5 and owner['failed_attempts'] == 2
    assert owner['constructed_pairs'] == 1 and owner['production_pairs'] == owner['canonical_jobs'] == 0
    assert sha((HERE / 'blocked-allocation-manifest.json').read_bytes()) == '56f01c68fc255ba0dd623caee5fb4190ba927e77ea095f49bb6388b049c47613'
    assert pins['counts'] == {'new_lean_jobs': 0, 'new_proof_pairs': 0, 'reused_constructed_pairs': 1}
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), 'live_root': args.live_root,
                      'root_foundations': len(pins['sources']), 'new_lean_jobs': 0,
                      'new_proof_pairs': 0, 'reused_constructed_pairs': 1}))


if __name__ == '__main__':
    main()
