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
    manifest = json.loads((HERE / 'stopping-fixture-manifest.json').read_text())
    for item in manifest['files']:
        path = Path(item['path'])
        assert not path.is_absolute() and '..' not in path.parts
        data = (HERE / path).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], str(path)
    pins = json.loads((HERE / 'stopping-fixture-source-pins.json').read_text())
    for item in pins['sources']:
        data = (HERE / item['snapshot']).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256']
        if args.live_root:
            assert (args.root / item['path']).read_bytes() == data, item['path']
    assert sha((HERE / 'inputs/SourceCurrentStoppingBuildRootedWriters.lean').read_bytes()) == '2ccd95c5fc0b271a4446b8f9a2b5732823171e933eacce687c874d7b1711f2ee'
    assert (HERE / 'inputs/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
    stems = ['stopping-fixture-direct-1', 'stopping-fixture-direct-2', 'stopping-fixture-direct-3', 'stopping-fixture-public-1']
    for index, stem in enumerate(stems):
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == (1 if index < 2 else 0)
        assert '-Dlinter.all=true' in meta['command'] and 'leanprover--lean4---v4.34.1/bin/lean' in meta['command'][0]
        assert sha((HERE / meta['source']).read_bytes()) == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    source = (HERE / 'stopping-rooted-kernels.lean').read_text()
    assert source == (HERE / 'stopping-fixture-direct-3.source.lean').read_text()
    assert not (HERE / 'stopping-fixture-direct-3.log').read_bytes()
    assert len(re.findall(r'rcases build_writer_or_prior ', source)) == 1
    assert len(re.findall(r'^theorem ', source, re.M)) == 1
    assert 'build source [] reserved = .pending blockedKey afterTarget' in source
    assert 'reserved.nodeRecords targetKey = none' in source
    private = source.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
    public = source.split('theorem actual_pending_writer :\n', 1)[1].split(' := checked_witness', 1)[0]
    assert private == public
    printer = (HERE / 'stopping-fixture-public-1.source.lean').read_text()
    assert printer.startswith(source) and printer == (HERE / 'stopping-fixture-public.lean').read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    name = 'MicroCFTA.StoppingRootedWritersFixture.actual_pending_writer'
    for prefix in ['#check @', '#print ', '#print axioms ']:
        assert prefix + name in printer
    log = (HERE / 'stopping-fixture-public-1.log').read_text()
    assert len(log.encode()) == 47906
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    for report in reports:
        names = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'stopping-fixture-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 4 and selection['failed_attempts'] == 2
    assert selection['constructed_pairs'] == 1 and selection['production_pairs'] == selection['canonical_jobs'] == 0
    assert selection['strict'] == 'stopping-fixture-direct-3' and selection['public_heads'] == [name]
    assert selection['groups'] == [{'name': 'stopping-fixture-public-1', 'pairs': 1, 'kind': 'constructed', 'full_proof': True}]
    peaks = (HERE / 'stopping-fixture-peaks-final.txt').read_text().splitlines()
    assert len(peaks) == 4 and all(' 4G ' in line for line in peaks)
    assert [line.rsplit(' ', 1)[-1] for line in peaks] == ['1', '1', '0', '0']
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']), 'live_root': args.live_root,
                      'foundation_sources': len(pins['sources']), 'constructed_pairs': 1,
                      'production_pairs': 0, 'lean_jobs': 4, 'failed_attempts': 2, 'canonical_jobs': 0}))


if __name__ == '__main__':
    main()
