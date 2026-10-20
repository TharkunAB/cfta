import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live-root', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'stopping-rooted-manifest.json').read_text())
    for item in manifest['files']:
        path = Path(item['path'])
        assert not path.is_absolute() and '..' not in path.parts
        data = (HERE / path).read_bytes()
        assert len(data) == item['bytes'] and digest(data) == item['sha256'], item['path']
    pins = json.loads((HERE / 'stopping-rooted-source-pins.json').read_text())
    for item in pins['sources']:
        data = (HERE / item['snapshot']).read_bytes()
        assert len(data) == item['bytes'] and digest(data) == item['sha256'], item['snapshot']
        if args.live_root:
            assert (args.root / item['path']).read_bytes() == data, item['path']
    source = (HERE / 'SourceCurrentStoppingBuildRootedWriters.lean').read_bytes()
    text = source.decode()
    assert '_private' not in text
    assert 'open SourceCurrentCompletedBuildRootedWriters (Written)' in text
    old = (HERE / 'inputs/SourceCurrentCompletedBuildRootedWriters.lean').read_text()
    old_private = old[old.index('private def Rooted'):old.index('/-- A selected cell is initial')]
    new_private = text[text.index('private def Rooted'):text.index('/-- A full Mu cell at the actual stopping state')]
    assert old_private == new_private
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    public_type = text[text.index('theorem build_writer_or_prior'):text.index(' := by', text.index('theorem build_writer_or_prior'))]
    assert '(actual :' not in public_type and '(selected : (build root initial before).state.nodeRecords key' in public_type
    assert 'Written root initial before (build root initial before).state key (.mu entry body depth ordinary)' in public_type
    assert (HERE / 'inputs/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
    for stem in ['stopping-rooted-direct-1', 'stopping-rooted-public-1']:
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0 and '-Dlinter.all=true' in meta['command']
        assert 'leanprover--lean4---v4.34.1/bin/lean' in meta['command'][0]
        limits = json.loads((HERE / meta['limits']).read_text())
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        assert digest((HERE / meta['source']).read_bytes()) == meta['sha256']
    assert source == (HERE / 'stopping-rooted-direct-1.source.lean').read_bytes()
    assert not (HERE / 'stopping-rooted-direct-1.log').read_bytes()
    printer = (HERE / 'stopping-rooted-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    assert (HERE / 'stopping-rooted-public.lean').read_text() == printer
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    name = 'MicroCFTA.SourceCurrentStoppingBuildRootedWriters.build_writer_or_prior'
    assert '#check @' + name in printer and '#print ' + name in printer and '#print axioms ' + name in printer
    log = (HERE / 'stopping-rooted-public-1.log').read_text()
    assert len(log.encode()) == 7102
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    selection = json.loads((HERE / 'stopping-rooted-selection.json').read_text())
    assert selection['finalized'] and selection['lean_jobs'] == 2 and selection['failed_attempts'] == 0
    assert selection['canonical_jobs'] == 0 and selection['constructed_pairs'] == 0
    assert selection['public_heads'] == [name]
    assert selection['groups'] == [{'name': 'stopping-rooted-public-1', 'pairs': 1, 'full_proof': True, 'kind': 'prototype-public'}]
    peaks = (HERE / 'stopping-rooted-peaks-final.txt').read_text().splitlines()
    assert len(peaks) == 2 and all(line.endswith(' 0') and ' 4G ' in line for line in peaks)
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']),
                      'foundation_sources': len(pins['sources']), 'live_root': args.live_root,
                      'public_pairs': 1, 'constructed_pairs': 0, 'lean_jobs': 2,
                      'failed_attempts': 0, 'canonical_jobs': 0}))


if __name__ == '__main__':
    main()
