import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = 'original-gate-projection-cap-review'
SOURCE = 'SourceCurrentOriginalGateProjectionCap.lean'
FINAL = 'f3b753ade1441826748505f13901964ffb44fe432a8999a34c487932f45055f5'
HEADS = ['MicroCFTA.SourceCurrentOriginalGateProjectionCap.' + n
         for n in ['project']]


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
        if installed.is_file():
            assert installed.read_bytes() == data, 'installed candidate'
    text = data.decode()
    assert len(text.splitlines()) == 315
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    public = text.split('theorem project ', 1)[1].split(':=', 1)[0]
    for token in [
        'Origin original prepared',
        'NodeTrace source reaches path original gateBefore false gateAfter',
        'SemanticReady gateBefore', 'Available gateBefore original',
        'SemanticReady before', 'CostHeap before', 'Available before prepared',
        'Guards before', 'Project (path.map Int.ofNat) prepared before result after',
        '∃ depth, Cap Plain depth result']:
        assert token in public, token
    assert public.count('Cap Plain') == 1
    for token in ['UnionNormal', 'free = []', 'NodeTrace source reaches path prepared', 'Grows']:
        assert token not in public, token
    for token in [
        'SourceCurrentPrimaryEndpointCap.endpoint_cap before',
        'SourceCurrentPrimaryEndpointCap.reaches_cap anchor',
        'SourceEndpointReachability.zero_clear source',
        'SourceCurrentGatePlainRegion.annotations anchor',
        'SourceEqualityProjectionLanguage.all₂_signed related index child selected',
        'SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain depth',
        'SourceCurrentConstrainedCapOpenExposure.head Plain depth',
        'SourceCurrentConstrainedCapProjectionGuard.read Plain',
        'SourceCurrentConstrainedCapProjectionGuard.head Plain',
        'Origin.rec', 'Project.rec', 'corridor_origin (gate_corridor']:
        assert token in text, token
    prep = json.loads((HERE / 'inputs/prep/source-pins.json').read_text())
    source_by_path = {item['path']: item for item in pins['sources']}
    for item in prep['sources']:
        check(HERE / 'inputs/prep', dict(item, path=item['snapshot']))
        if item['path'] in source_by_path:
            assert item['sha256'] == source_by_path[item['path']]['sha256']
    owner = HERE / 'inputs/owner'
    for stem in ['gate-cap-direct-2', 'gate-cap-public-1']:
        meta = json.loads((owner / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
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
    assert not (owner / 'gate-cap-direct-2.log').read_bytes()
    assert (owner / 'gate-cap-direct-2.source.lean').read_bytes() == data
    selection = json.loads((owner / 'gate-cap-selection.json').read_text())
    assert selection['finalized'] is True
    assert selection['source_sha256'] == FINAL and selection['public_heads'] == HEADS
    assert selection['selected_strict'] == 'gate-cap-direct-2'
    assert selection['selected_public'] == 'gate-cap-public-1'
    assert selection['lean_jobs'] == 3 and selection['failed_lean_checks'] == 1
    assert selection['public_pairs'] == 1 and selection['constructed_pairs'] == 0
    printer = (owner / 'gate-cap-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (owner / 'gate-cap-public-1.log').read_text()
    assert len(log.encode()) == 8966
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1
        report = re.search(r"'" + re.escape(head) + r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
        assert report, head
        names = set() if report.group(1) is None else {
            re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in report.group(1).split(',') if n.strip()}
        assert names == {'propext', 'Classical.choice', 'Quot.sound'}, (head, names)
        kind = 'theorem'
        block = log.split(kind + ' ' + head, 1)[1].split("'" + head + "'", 1)[0]
        typ, proof = block.split(':=', 1)
        assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'review': 'independent', 'material_issues': 0,
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'reused_full_public_pairs': 1, 'selected_strict_log_bytes': 0,
                      'full_public_log_bytes': 8966, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
