import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'], ('bytes', path)
    assert digest(data) == item['sha256'], ('hash', path)
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    assert manifest['finalized'] is True
    assert manifest['status'] == 'source-audit-only'
    assert manifest['owned_lean_lake_commands'] == manifest['owned_public_pairs'] == 0
    for item in manifest['files']:
        check(HERE / item['path'], item)
    pins = json.loads((HERE / 'source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    sources = {}
    range_count = 0
    for item in manifest['sources']:
        data = check(HERE / item['snapshot'], item)
        if args.live:
            check(args.root / item['path'], item)
        lines = data.decode().splitlines(keepends=True)
        for section in item['ranges']:
            start, end = section['start'], section['end']
            assert 1 <= start <= end <= len(lines)
            block = ''.join(lines[start-1:end]).encode()
            assert len(block) == section['bytes']
            assert digest(block) == section['sha256']
            range_count += 1
        sources[Path(item['path']).stem] = data.decode()
    assert sources['lean-toolchain'].strip() == 'leanprover/lean4:v4.34.1'
    raw = sources['SourceCurrentRequiredRawCorridor']
    assert '| full (path value) (bounded : ∃ depth, Cap Plain depth value)' in raw
    assert 'select row.children index = some child → RawCorridor path child' in raw
    capped = sources['SourceCurrentCappedProjectionPositivePosition']
    for token in ['theorem root ', 'theorem child ', '(bounded : Cap Plain capDepth value)',
                  'PositiveAt value (path ++ childIndex :: residual)']:
        assert token in capped
    spine = sources['SourceCurrentProjectionReadSpine']
    for token in ['inductive Spine', 'sourceIndex', 'operandIndex', 'rawIndex', 'readIndex',
                  'projectPrefix', 'projectSuffix', 'readPrefix', 'readSuffix',
                  'theorem project ']:
        assert token in spine
    effects = sources['SourceEqualityProjectionCosts']
    for name in ['rows_effects', 'readAll_effects', 'project_effects', 'union_effects']:
        assert 'theorem ' + name in effects
    guards = sources['SourceCurrentConstrainedCapProjectionGuard']
    assert 'theorem node ' in guards and 'theorem readAll ' in guards
    heap = sources['SourceCurrentConstrainedCapGuardHeap']
    assert 'state.nodeRecords key = some (.mu entry body depth ordinary)' in heap
    growth = sources['InternedConstructorTemplates']
    assert 'nodeRecords : Extends before.nodeRecords after.nodeRecords' in growth
    plan = (HERE / 'plan.md').read_text()
    for phrase in ['No new Lean theorem is proved', 'No public caller supplies a Spine',
                   'does not transport PositiveAt backward',
                   'This is backward restriction of an existing record property',
                   'No checked counterexample or new source family is claimed']:
        assert phrase in plan
    assert not list(HERE.glob('*.lean'))
    print(json.dumps({'status': 'PASS', 'live': args.live,
                      'pins': len(manifest['files']) + len(manifest['sources']),
                      'source_files': len(manifest['sources']), 'source_ranges': range_count,
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'implementation_status': 'unproved source-audit plan',
                      'retained_nonlean_metadata_diagnostics': 1}))


if __name__ == '__main__':
    main()
