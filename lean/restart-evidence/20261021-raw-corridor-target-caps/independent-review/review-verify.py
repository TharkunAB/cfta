#!/usr/bin/env python3
"""Check frozen source and selected proof evidence without invoking Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path, item):
    assert path.is_file() and path.stat().st_size == item['bytes'], str(path)
    assert digest(path) == item['sha256'], str(path)


def load(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = load(HERE / 'review-manifest.json')
    for item in manifest['files']:
        check(HERE / item['path'], item)
    pins = load(HERE / 'review-source-pins.json')['files']
    assert len(pins) == 55 and len({item['path'] for item in pins}) == 55
    for item in pins:
        check(HERE / 'inputs/root' / item['path'], item)
        if args.live:
            check(args.root / item['path'], item)
    selection = load(HERE / 'review-selection.json')
    assert selection['finalized'] and selection['review_lean_jobs'] == 0
    assert selection['authored_public_pairs'] == 0 and selection['reused_public_heads'] == 7
    assert selection['reused_unique_owner_lean_jobs'] == 11 and selection['reused_owner_canonical_jobs'] == 3
    heads = 0
    for component in selection['components']:
        base = HERE / 'inputs/components' / component['name']
        prefix = component['prefix']
        chosen = load(base / (prefix + '-selection.json'))
        assert chosen['finalized'] and chosen['source_sha256'] == component['source_sha256']
        assert chosen['public_heads'] == component['heads']
        assert digest(base / (prefix + '-manifest.json')) == component['owner_manifest_sha256']
        source = base / component['source']
        text = source.read_text()
        assert digest(source) == component['source_sha256'] and len(text.splitlines()) == component['lines']
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
        if args.live:
            installed = args.root / 'lean/MicroCFTA' / source.name
            if installed.exists():
                assert installed.read_bytes() == source.read_bytes()
        for field in ['strict', 'canonical', 'public']:
            stem = component[field]
            meta = load(base / (stem + '.json'))
            assert meta['exit_code'] == 0 and digest(base / meta['source']) == meta['sha256']
            assert meta['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
            assert '-Dlinter.all=true' in meta['command']
            assert meta['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
            assert load(base / meta['limits']) == {
                'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
            usage = load(base / (stem + '.usage.json'))
            assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
            end = datetime.datetime.fromisoformat(meta['observed_at'])
            sampled = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
            if 'started_at' in meta:
                start = datetime.datetime.fromisoformat(meta['started_at'])
                assert 0 <= (end - start).total_seconds() < 300
                assert 0 <= (start - sampled).total_seconds() < 120
            else:
                assert component['name'] == 'target'
                assert 0 <= (end - sampled).total_seconds() < 300
            if field != 'public':
                assert (base / meta['log']).read_bytes() == b''
                assert (base / meta['source']).read_bytes() == source.read_bytes()
            if field == 'canonical':
                assert '-R' in meta['command'] and '-o' in meta['command']
        meta = load(base / (component['public'] + '.json'))
        printer = (base / meta['source']).read_text()
        assert printer.startswith(text)
        for option in OPTIONS:
            assert 'set_option ' + option in printer
        log = (base / meta['log']).read_text()
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        assert len(reports) == len(component['heads'])
        for head in component['heads']:
            heads += 1
            for directive in ['#check @', '#print ', '#print axioms ']:
                assert printer.count(directive + head + '\n') == 1
            matched = [names for name, names in reports if name == head]
            assert len(matched) == 1
            names = {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in matched[0].split(',') if name.strip()}
            assert names == STANDARD, (head, names)
            checked = re.search(r'@?' + re.escape(head) + r' :', log)
            assert checked, head
            checked_type = log[checked.end():].split('\ntheorem ', 1)[0].split('\ninductive ', 1)[0]
            assert '_private' not in checked_type
    assert heads == 7
    raw = (HERE / 'inputs/components/raw/SourceCurrentRequiredRawCorridor.lean').read_text()
    assert 'RawCorridor (index::path)' in raw and '∀ row ∈ rows, ∀ child, select row.children index = some child' in raw
    assert 'false_selected' in raw and 'mapped.indexed' in raw and 'All₂ Origin originals prepared' in raw
    projected = (HERE / 'inputs/components/projection/SourceCurrentRawCorridorProjectionCap.lean').read_text()
    assert 'Guards after ∧ ∀ value ∈ results, Finite value' in projected
    assert '∀ value, select values index = some value → RawCorridor path value' in projected
    assert 'free = []' not in projected and 'OpenExposure.head' in projected and 'OpenExposure.nodeEdges' in projected
    target = (HERE / 'inputs/components/target/SourceCurrentRawCorridorSharedTargetCap.lean').read_text()
    for token in ['operandPaths_nonroot record coherent active', 'Ready formulas solver inventory record values base before',
                  'hit present => exact ⟨stored,stored.slots action value present⟩', 'ConstrainedCapMemoMerge.retained Plain',
                  'CurrentNative.step (max headDepth tailDepth)', 'SourceCurrentRequiredSharedTargetCap.Stored']:
        assert token in target, token
    review = (HERE / 'review.md').read_text()
    assert 'zero new Lean jobs' in review and 'does not yet prove' in review
    assert manifest['scope'] == {'review_lean_jobs': 0, 'authored_public_pairs': 0, 'reused_public_heads': 7}
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'review_lean_jobs': 0, 'authored_public_pairs': 0,
                      'reused_public_heads': 7, 'reused_unique_owner_lean_jobs': 11,
                      'reused_owner_canonical_jobs': 3, 'standard_axioms_only': True}, sort_keys=True))


if __name__ == '__main__':
    main()
