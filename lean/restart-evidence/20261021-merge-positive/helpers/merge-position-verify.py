#!/usr/bin/env python3
"""Verify the private helper package without running Lean."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path: Path, pin: dict) -> None:
    assert path.is_file(), str(path)
    assert path.stat().st_size == pin['bytes'], str(path)
    assert digest(path) == pin['sha256'], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'merge-position-manifest.json').read_text())
    for pin in manifest['files']:
        check(here / pin['path'], pin)
    pins = json.loads((here / 'merge-position-source-pins.json').read_text())['files']
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)

    selection = json.loads((here / 'merge-position-selection.json').read_text())
    assert selection == {
        'finalized': True,
        'source_sha256': 'd5907f4e66b880271326b1058f76a036e04ce8a10998ff3a290fb1ab91f07d09',
        'snippet_sha256': '17774382af913b87902b9440ca18aebb2011a3a9bb543e6cc01c2e56ee83064e',
        'selected': ['merge-position-direct-2'],
        'unselected': ['merge-position-direct-1'],
        'lean_jobs': 2, 'failed_lean_checks': 1,
        'canonical_jobs': 0, 'public_pairs': 0, 'constructed_pairs': 0,
        'auxiliary_full_jobs': 0,
    }
    source = here / 'SourceCurrentMergePositionHelpers.lean'
    assert digest(source) == selection['source_sha256']
    text = source.read_text()
    helpers = re.findall(r'^private theorem (\w+)', text, re.M)
    assert helpers == ['columns_indexed', 'makeNode_positive', 'rows_positive',
                       'ordinary_edges_rows', 'flatten_positive',
                       'ordinaryUnion_positive', 'makeUnion_positive']
    assert not re.search(r'^(?:theorem|def|axiom)\s', text, re.M)
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b', text)
    snippet = 'open InternedEdgeResidency (nodeEdges)\nopen InternedNestedFacts (Facts)\n\n'
    snippet += text[text.index('private theorem columns_indexed'):text.index('end MicroCFTA.')]
    assert (here / 'helpers.lean.txt').read_text() == snippet.rstrip('\n')
    assert digest(here / 'helpers.lean.txt') == selection['snippet_sha256']
    for evidence in ['row[index]? = some value', 'PositiveAt input path',
                     'InternedGateRank.requested_fields', 'InternedNormalizationFree.value_lists_equal',
                     'available_after_run', 'change InternedRecordCoherence.NodeFields key entry result']:
        assert evidence in text, evidence
    assert sorted(p.name for p in here.glob('merge-position-direct-*.json')
                  if not p.name.endswith(('.limits.json', '.usage.json'))) == [
                      'merge-position-direct-1.json', 'merge-position-direct-2.json']
    for number, status in [(1, 1), (2, 0)]:
        stem = f'merge-position-direct-{number}'
        receipt = json.loads((here / (stem + '.json')).read_text())
        assert receipt['exit_code'] == status
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert receipt['source'] == stem + '.source.lean'
        assert digest(here / receipt['source']) == receipt['sha256']
        assert receipt['log'] == stem + '.log'
        assert receipt['limits'] == stem + '.limits.json'
        limits = json.loads((here / receipt['limits']).read_text())
        assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = json.loads((here / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
        if number == 2:
            assert (here / receipt['log']).stat().st_size == 0
            assert (here / receipt['source']).read_bytes() == source.read_bytes()
        else:
            assert 'error:' in (here / receipt['log']).read_text()
    assert not list(here.glob('*public-*.json'))
    print(json.dumps({'status': 'PASS', 'live': args.live,
                      'local_pins': len(manifest['files']), 'root_pins': len(pins),
                      'lean_jobs': 2, 'failed_lean_checks': 1,
                      'public_pairs': 0, 'constructed_pairs': 0,
                      'canonical_jobs': 0, 'auxiliary_full_jobs': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
