import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentRawCorridorProjectionCap.lean'
FINAL = 'e4a19e65aaeda9d1305e8fb1a7f784fdb5bd9b39953d8af2dab04cede4c15563'
RAW_FINAL = '944e4545b4e8fe73e61b278ba843e3b7e1fe8bea8e0f14416a534f11c6f3a7fb'
HEADS = ['MicroCFTA.SourceCurrentRawCorridorProjectionCap.' + name for name in ['project', 'forest']]
STEMS = ['raw-projection-direct-1', 'raw-projection-direct-2',
         'raw-projection-canonical-1', 'raw-projection-public-1']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], ('bytes', item['path'])
    assert digest(data) == item['sha256'], ('hash', item['path'])


def receipt(base, stem, exit_code):
    meta = json.loads((base / (stem + '.json')).read_text())
    assert meta['exit_code'] == exit_code, stem
    assert digest((base / meta['source']).read_bytes()) == meta['sha256']
    assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
    assert '-Dlinter.all=true' in meta['command']
    assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
    assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
    assert json.loads((base / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    start = datetime.datetime.fromisoformat(meta['started_at'])
    end = datetime.datetime.fromisoformat(meta['observed_at'])
    assert 0 <= (end - start).total_seconds() < 300
    usage = json.loads((base / (stem + '.usage.json')).read_text())
    assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    observed = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
    assert 0 <= (start - observed).total_seconds() < 120
    return meta


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'raw-projection-manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        check(HERE, item)
    pins = json.loads((HERE / 'raw-projection-source-pins.json').read_text())
    assert pins['files'] == manifest['sources']
    for item in manifest['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    data = (HERE / SOURCE).read_bytes()
    assert digest(data) == FINAL
    text = data.decode()
    assert len(text.splitlines()) == 176
    assert len(re.findall(r'^theorem ', text, re.M)) == 2
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / SOURCE
        if installed.exists():
            assert installed.read_bytes() == data
    raw = HERE / 'inputs/raw-dependency/SourceCurrentRequiredRawCorridor.lean'
    assert digest(raw.read_bytes()) == RAW_FINAL
    if args.live:
        installed_raw = args.root / 'lean/MicroCFTA' / raw.name
        if installed_raw.exists():
            assert installed_raw.read_bytes() == raw.read_bytes()
    for stem in STEMS:
        meta = receipt(HERE, stem, 1 if stem.endswith('direct-1') else 0)
        if stem != 'raw-projection-public-1':
            assert meta['sha256'] == FINAL
    assert not (HERE / 'raw-projection-direct-2.log').read_bytes()
    assert not (HERE / 'raw-projection-canonical-1.log').read_bytes()
    assert 'object file' in (HERE / 'raw-projection-direct-1.log').read_text()
    assert 'SourceCurrentPrimaryEndpointCap.olean' in (HERE / 'raw-projection-direct-1.log').read_text()
    canonical = json.loads((HERE / 'raw-projection-canonical-1.json').read_text())
    assert '-R' in canonical['command'] and '-o' in canonical['command']
    assert canonical['output'] == 'import-tree/MicroCFTA/SourceCurrentRawCorridorProjectionCap.olean'
    assert (HERE / canonical['output']).stat().st_size > 0
    dependency = receipt(HERE / 'inputs/raw-dependency', 'raw-corridor-canonical-1', 0)
    assert dependency['sha256'] == RAW_FINAL
    assert not (HERE / 'inputs/raw-dependency/raw-corridor-canonical-1.log').read_bytes()
    assert '-R' in dependency['command'] and '-o' in dependency['command']
    layout = json.loads((HERE / 'raw-projection-import-layout.json').read_text())
    assert layout['external_tree_not_archived'] is True
    assert digest((HERE / layout['raw_snapshot']).read_bytes()) == layout['raw_sha256']
    assert all(not path.is_symlink() for path in HERE.rglob('*'))
    selection = json.loads((HERE / 'raw-projection-selection.json').read_text())
    assert selection['finalized'] is True and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == HEADS
    assert selection['selected_strict'] == 'raw-projection-direct-2'
    assert selection['selected_public'] == 'raw-projection-public-1'
    assert selection['selected_canonical'] == 'raw-projection-canonical-1'
    assert selection['lean_jobs'] == 4 and selection['failed_lean_checks'] == 1
    assert selection['import_failures'] == 1 and selection['proof_elaboration_failures'] == 0
    assert selection['canonical_jobs'] == 1 and selection['public_pairs'] == 2
    assert selection['constructed_pairs'] == 0 and selection['reused_dependency_canonical_jobs'] == 1
    public_project = text.split('theorem project ', 1)[1].split(':=', 1)[0]
    for token in ['Project path value before result after', 'SemanticReady before', 'CostHeap before',
                  'Available before value', 'Guards before', 'RawCorridor path value',
                  '∃ depth, Cap Plain depth result']:
        assert token in public_project, token
    public_forest = text.split('theorem forest ', 1)[1].split(':=', 1)[0]
    assert 'Forest (index::path) values before result after' in public_forest
    assert '∀ value, select values index = some value → RawCorridor path value' in public_forest
    assert 'free = []' not in text
    for token in ['SourceCurrentConstrainedCapOpenExposure.nodeEdges',
                  'SourceCurrentConstrainedCapOpenExposure.head',
                  'SourceCurrentConstrainedCapProjectionGuard.node Plain first',
                  'Guards after ∧ ∀ value ∈ results, Finite value',
                  'SourceCurrentConstrainedCap.makeNode Plain depth']:
        assert token in text, token
    printer = (HERE / 'raw-projection-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (HERE / 'raw-projection-public-1.log').read_text()
    assert len(log.encode()) == 77308
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1
        report = re.search(r"'" + re.escape(head) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
        assert report, head
        names = {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in report.group(1).split(',') if name.strip()}
        assert names == {'propext', 'Classical.choice', 'Quot.sound'}, (head, names)
        block = log.split('theorem ' + head, 1)[1].split("'" + head + "'", 1)[0]
        typ, proof = block.split(':=', 1)
        assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'owned_lean_jobs': 4, 'owned_failed_lean_checks': 1,
                      'owned_import_failures': 1, 'owned_proof_elaboration_failures': 0,
                      'owned_public_pairs': 2, 'owned_constructed_pairs': 0, 'owned_canonical_jobs': 1,
                      'reused_dependency_canonical_jobs': 1, 'selected_strict_log_bytes': 0,
                      'full_public_log_bytes': 77308, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
