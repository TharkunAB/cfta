#!/usr/bin/env python3
"""Check frozen actual class corridor evidence without invoking Lean."""
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

FINAL = 'bc0701959646a61bee767cf6b80db04b314302d16891efd7aa539ca314eacd84'
HEAD = 'MicroCFTA.SourceCurrentClassEndpointCorridors.class_reads'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(path, item):
    assert path.is_file() and path.stat().st_size == item['bytes'], str(path)
    assert digest(path) == item['sha256'], str(path)


def load(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = load(here / 'class-corridor-manifest.json')
    for item in manifest['files']:
        check(here / item['path'], item)
    pins = load(here / 'class-corridor-source-pins.json')['files']
    assert len(pins) == 69 and len({item['path'] for item in pins}) == 69
    for item in pins:
        check(here / 'inputs/root' / item['path'], item)
        if args.live:
            check(args.root / item['path'], item)
    selection = load(here / 'class-corridor-selection.json')
    assert selection['finalized'] and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == [HEAD] and selection['public_kinds'] == ['theorem']
    assert (selection['lean_jobs'], selection['failed_lean_checks'], selection['warning_checks']) == (5, 2, 1)
    assert (selection['public_pairs'], selection['constructed_pairs'], selection['canonical_jobs']) == (1, 0, 0)
    assert selection['selected_strict'] == 'class-corridor-direct-4'
    assert selection['selected_public'] == 'class-corridor-public-1'
    assert selection['unselected_successes'] == ['class-corridor-direct-3']
    source = here / selection['source']
    text = source.read_text()
    assert digest(source) == FINAL and len(text.splitlines()) == 420
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['class_reads']
    assert not re.search(r'^(?:structure|inductive|def|axiom)\s|\b(?:sorry|admit|native_decide|trustCompiler)\b', text, re.M)
    public = text.split('theorem class_reads', 1)[1].split(':= by', 1)[0]
    for forbidden in ['Preserves', 'Masks', 'NodeGoal', 'Finite', 'inputCap', 'capturedCaps', 'outputCap', '.free = []']:
        assert forbidden not in public
    for token in ['Coherent record', 'Nontrivial record.paths', 'ClassReads formulas solver actual memos final',
                  'CurrentNative.At Plain before', 'MemoMerge.Stored Plain memo',
                  'index::path ∈ record.paths', 'select values (Int.ofNat index) = some value',
                  'RawCorridor (path.map Int.ofNat) value',
                  'All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results']:
        assert token in public, token
    for token in ['SourceCurrentRawCorridorSharedTargetCap.force_receipt known masks coherent active first ready stored',
                  'CurrentNative.step (max targetDepth inputDepth)',
                  'hasLeaf := nonempty', 'SourceCurrentConstrainedCapOpenExposure.head Plain depth actual',
                  'rows_selected related index tail children', 'canonicalEdges (surviving results)',
                  'SourceEqualityEditCompiledPaths.build_leaves',
                  'SourceCurrentAllocatedSharedEditEffects.node_effects',
                  'SourceCurrentAllocatedSharedEditEffects.children_effects',
                  'SourceCurrentAllocatedSharedEditEffects.rows_effects',
                  'SourceCurrentAllocatedClassEdits.verified', 'ListAtLeaves (compiled record) values']:
        assert token in text, token
    attempts = selection['attempts']
    assert attempts == {'class-corridor-direct-1': 1, 'class-corridor-direct-2': 1,
                        'class-corridor-direct-3': 0, 'class-corridor-direct-4': 0, 'class-corridor-public-1': 0}
    actual = {p.stem for p in here.glob('class-corridor-*.json')
              if re.fullmatch(r'class-corridor-(direct|public)-\d+', p.stem)}
    assert actual == set(attempts)
    for stem, expected in attempts.items():
        receipt = load(here / (stem + '.json'))
        assert receipt['exit_code'] == expected and digest(here / receipt['source']) == receipt['sha256']
        assert receipt['source'] == stem + '.source.lean'
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert '-Dlinter.all=true' in receipt['command']
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert load(here / receipt['limits']) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = load(here / (stem + '.usage.json'))
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        start = datetime.datetime.fromisoformat(receipt['started_at'])
        end = datetime.datetime.fromisoformat(receipt['observed_at'])
        sample = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
        assert 0 <= (end - start).total_seconds() < 300
        assert 0 <= (start - sample).total_seconds() < 120
    assert (here / 'class-corridor-direct-4.log').read_bytes() == b''
    assert (here / 'class-corridor-direct-4.source.lean').read_bytes() == source.read_bytes()
    assert 'warning:' in (here / 'class-corridor-direct-3.log').read_text()
    for stem in ['class-corridor-direct-1', 'class-corridor-direct-2']:
        assert 'error:' in (here / (stem + '.log')).read_text() or 'error(' in (here / (stem + '.log')).read_text()
    printer = (here / 'class-corridor-public-1.source.lean').read_text()
    assert printer == (here / 'class-corridor-public.lean').read_text() and printer.startswith(text)
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert 'set_option ' + option in printer
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD + '\n') == 1
    log_path = here / 'class-corridor-public-1.log'
    assert log_path.stat().st_size == selection['printer_bytes'] == 164280
    assert digest(log_path) == selection['printer_sha256'] == 'c0018224c1732eb404c96d40c5f90a49185673bb779443bb27efc002c25e15ba'
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked = log.split('@' + HEAD + ' :', 1)[1].split('\ntheorem ' + HEAD, 1)[0]
    assert '_private' not in checked and 'ClassEndpointCorridors.Preserves' not in checked
    block = log.split('\ntheorem ' + HEAD, 1)[1].split("'" + HEAD + "' depends on axioms", 1)[0]
    typ, proof = block.split(':=', 1)
    assert '_private' not in typ and typ.strip() and proof.strip()
    axioms = [{name.strip() for name in re.sub(r'\.\{[^}]*\}', '', report).split(',')}
              for report in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)]
    assert axioms == [{'propext', 'Classical.choice', 'Quot.sound'}]
    layout = load(here / 'class-corridor-import-layout.json')
    assert layout['owned_dependency_lean_jobs'] == 0 and layout['reused_dependency_lean_jobs'] == 11
    for item in layout['artifacts']:
        check(here / item['path'], item)
    runner = (here / 'class-corridor-run-check.py').read_text()
    assert "LEAN_PATH='/tmp/mcfta-raw-corridor-target-imports:'" in runner
    for folder, prefix, sha in [('raw','raw-corridor','944e4545b4e8fe73e61b278ba843e3b7e1fe8bea8e0f14416a534f11c6f3a7fb'),
                                ('projection','raw-projection','e4a19e65aaeda9d1305e8fb1a7f784fdb5bd9b39953d8af2dab04cede4c15563'),
                                ('target','target','7187a93a97be5cd1e1622e3945037b0c8fbb41b48a91b630c832fd054a61e804')]:
        base = here / 'inputs/dependencies' / folder
        chosen = load(base / (prefix + '-selection.json'))
        assert chosen['finalized'] and chosen['source_sha256'] == sha
        assert digest(base / chosen['source']) == sha
        if args.live:
            installed = args.root / 'lean/MicroCFTA' / chosen['source']
            if installed.exists():
                assert digest(installed) == sha
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / source.name
        if installed.exists():
            assert digest(installed) == FINAL
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),
                      'lean_jobs':5,'failed_lean_checks':2,'warning_checks':1,'public_pairs':1,
                      'constructed_pairs':0,'canonical_jobs':0,'full_public_heads':1,'standard_axioms':3},sort_keys=True))


if __name__ == '__main__':
    main()
