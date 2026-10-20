import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEAD = 'MicroCFTA.WarmOwnerSelectionFixture.actual_warm_owner_selection'
SOURCE = 'warm-owner-selection-kernels.lean'


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'warm-owner-kernels-manifest.json').read_text())
    for entry in manifest['files']:
        check(HERE, entry)
    for entry in manifest['sources']:
        check(HERE / 'inputs/root', entry)
        if args.live:
            check(args.root, entry)
    assert json.loads((HERE / 'warm-owner-kernels-source-pins.json').read_text())['files'] == manifest['sources']
    selection = json.loads((HERE / 'warm-owner-kernels-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == [HEAD]
    assert selection['lean_jobs'] == 3 and selection['failed_checks'] == 1
    assert selection['new_public_pairs'] == 0 and selection['constructed_pairs'] == 1
    assert selection['canonical_jobs'] == 0 and selection['new_source_families'] == 0
    source = (HERE / SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == selection['source_sha256']
    assert (HERE / 'warm-owner-kernels-direct-2.source.lean').read_text() == source
    assert len(source.splitlines()) == 282
    assert source.count('SourceCurrentOuterOwnerSelection.selected ') == 1
    assert source.count('theorem actual_warm_owner_selection :') == 1
    assert 'nodeCall ' not in source and 'walk ' not in source
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler', source)
    checked_type = source.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
    public_type = source.split('theorem actual_warm_owner_selection :\n', 1)[1].split(' := checked_witness', 1)[0]
    assert checked_type == public_type
    old = (HERE / 'inputs/root/lean/MicroCFTA/SourceCurrentOuterOriginalRepeat.lean').read_text()
    family = source.split('private def plain :', 1)[1].split('private def inherited', 1)[0]
    old_family = old.split('private def plain :', 1)[1].split('private def inherited', 1)[0]
    assert family == old_family
    identity = json.loads((HERE / 'warm-owner-kernels-type-check.json').read_text())
    assert identity['private_public_type_identical'] and identity['one_selected_consumer']
    assert identity['original_repeat_family_block_identical']
    assert hashlib.sha256(family.encode()).hexdigest() == identity['family_block_sha256']
    for name, expected in selection['attempts'].items():
        metadata = json.loads((HERE / (name + '.json')).read_text())
        assert metadata['exit_code'] == expected
        assert metadata['wrapper'][metadata['wrapper'].index('--mem') + 1] == '4G'
        assert metadata['wrapper'][metadata['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / metadata['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((HERE / (name + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        frozen = (HERE / metadata['source']).read_bytes()
        assert hashlib.sha256(frozen).hexdigest() == metadata['sha256']
        assert '-Dlinter.all=true' in metadata['command']
        assert metadata['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
    assert not (HERE / 'warm-owner-kernels-direct-2.log').read_bytes()
    failed = (HERE / 'warm-owner-kernels-direct-1.log').read_text()
    assert 'Values' in failed and 'error' in failed
    printer = (HERE / 'warm-owner-kernels-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    log = (HERE / 'warm-owner-kernels-public-1.log').read_text()
    assert len(log.encode()) == selection['public_log_bytes']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    printed = log.split('theorem ' + HEAD, 1)[1]
    printed_type, proof = printed.split(':=', 1)
    assert printed_type.strip() and proof.strip()
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', reports[0]).strip())) == {
        'propext', 'Classical.choice', 'Quot.sound'}
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'new_public_pairs': 0, 'constructed_pairs': 1, 'lean_jobs': 3,
                      'failed_checks': 1, 'canonical_jobs': 0, 'new_source_families': 0, 'live': args.live}))


if __name__ == '__main__':
    main()
