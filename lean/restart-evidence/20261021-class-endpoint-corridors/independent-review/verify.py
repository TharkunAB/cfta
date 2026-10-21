import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentClassEndpointCorridors.lean'
FINAL = 'bc0701959646a61bee767cf6b80db04b314302d16891efd7aa539ca314eacd84'
HEAD = 'MicroCFTA.SourceCurrentClassEndpointCorridors.class_reads'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], ('bytes', item['path'])
    assert digest(data) == item['sha256'], ('hash', item['path'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    assert manifest['finalized'] is True
    assert manifest['owned_lean_lake_commands'] == 0 and manifest['owned_public_pairs'] == 0
    for item in manifest['files']:
        check(HERE, item)
    for item in manifest['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    pins = json.loads((HERE / 'source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    candidate = pins['candidate']
    data = (HERE / candidate['snapshot']).read_bytes()
    assert digest(data) == candidate['sha256'] == FINAL
    assert len(data) == candidate['bytes']
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / SOURCE
        if installed.exists():
            assert installed.read_bytes() == data
    text = data.decode()
    assert len(text.splitlines()) == 420
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    public = text.split('theorem class_reads ', 1)[1].split(':=', 1)[0]
    for token in [
        'SourceEqualityClassOrder.Coherent record', 'EqualityNormalize.Nontrivial record.paths',
        'SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final',
        'SourceCurrentConjunctionClassScan.Ready before',
        'SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before',
        'Values before.native.machine.heap values',
        '∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values',
        'SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo',
        'SourceCurrentConstrainedCapCurrentNative.At Plain before',
        'SourceCurrentConstrainedCapMemoMerge.Stored Plain memo',
        'select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value',
        'SourceCurrentAllocatedClassEdits.Receipt formulas solver next record values before memo results after saved memos final',
        'SourceCurrentConstrainedCapCurrentNative.At Plain after',
        'SourceCurrentConstrainedCapMemoMerge.Stored Plain saved',
        'All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results']:
        assert token in public, token
    for token in ['ClassTrace', 'NodeTrace', 'false scanHeap', 'Finite', 'Preserves', 'AtLeaves']:
        assert token not in public, token
    for token in [
        'private def Preserves (original result : Node) := ∀ path, RawCorridor path original → RawCorridor path result',
        'SourceEqualityEditCompiledPaths.build_leaves _ (compiled_disjoint record coherent)',
        'InternedEdgeResidency.identifyNode_readback (first::rest) state coherent linked',
        'SourceCurrentRawCorridorSharedTargetCap.force_receipt known masks coherent active first ready stored',
        'SourceCurrentConstrainedCapCurrentNative.step (max targetDepth inputDepth)',
        'root_finite (placed [] path',
        'have hasLeaf := nonempty',
        'SourceCurrentConstrainedCapOpenExposure.head Plain depth actual',
        'root_finite (later.2 [] (.full [] _',
        'InternedShallowValues.makeEdge_children edge.entry.key.symbol edge.entry.key.constraint values',
        'exact ChildrenReads.rec',
        'SourceCurrentAllocatedClassEdits.verified formulas solver inventory record coherent active reads',
        'SourceCurrentRequiredSharedTargetCap.initial_stored before memo current merged',
        'initialReady available safe valid available masks initialStore placed']:
        assert text.count(token) == 1, token
    owner = HERE / 'inputs/owner'
    stems = [f'class-corridor-direct-{n}' for n in range(1, 5)] + ['class-corridor-public-1']
    for stem in stems:
        meta = json.loads((owner / (stem + '.json')).read_text())
        expected = 1 if stem in stems[:2] else 0
        assert meta['exit_code'] == expected, stem
        assert digest((owner / meta['source']).read_bytes()) == meta['sha256']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((owner / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        start = datetime.datetime.fromisoformat(meta['started_at'])
        end = datetime.datetime.fromisoformat(meta['observed_at'])
        assert 0 <= (end - start).total_seconds() < 300
        usage = json.loads((owner / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        observed = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
        assert 0 <= (start - observed).total_seconds() < 120
    assert not (owner / 'class-corridor-direct-4.log').read_bytes()
    assert (owner / 'class-corridor-direct-4.source.lean').read_bytes() == data
    selection = json.loads((owner / 'class-corridor-selection.json').read_text())
    assert selection['finalized'] is True and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == [HEAD]
    assert selection['selected_strict'] == 'class-corridor-direct-4'
    assert selection['selected_public'] == 'class-corridor-public-1'
    assert selection['lean_jobs'] == 5 and selection['failed_lean_checks'] == 2
    assert selection['warning_checks'] == 1
    assert selection['unselected_successes'] == ['class-corridor-direct-3']
    warnings = (owner / 'class-corridor-direct-3.log').read_text()
    assert 'warning:' in warnings and 'error:' not in warnings
    assert selection['public_pairs'] == 1 and selection['constructed_pairs'] == 0
    printer = (owner / 'class-corridor-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD + '\n') == 1
    log = (owner / 'class-corridor-public-1.log').read_text()
    assert len(log.encode()) == 164280
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    report = re.search(r"'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert report
    names = {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in report.group(1).split(',') if name.strip()}
    assert names == {'propext', 'Classical.choice', 'Quot.sound'}
    block = log.split('theorem ' + HEAD, 1)[1].split("'" + HEAD + "'", 1)[0]
    typ, proof = block.split(':=', 1)
    assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'review': 'independent', 'material_issues': 0,
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'reused_full_public_pairs': 1, 'reused_actual_lean_jobs': 5,
                      'reused_lean_failures': 2, 'reused_unselected_warning_checks': 1,
                      'selected_strict_log_bytes': 0,
                      'full_public_log_bytes': 164280, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
