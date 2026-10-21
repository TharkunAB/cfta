#!/usr/bin/env python3
"""Check an unproved source-pinned plan without invoking Lean."""
import argparse
import hashlib
import json
from pathlib import Path


def check(path, item):
    assert path.is_file() and path.stat().st_size == item['bytes'], str(path)
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], str(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'plan-manifest.json').read_text())
    for item in manifest['files']:
        check(here / item['path'], item)
    pins = json.loads((here / 'plan-source-pins.json').read_text())['files']
    assert len(pins) == 42 and len({item['path'] for item in pins}) == 42
    for item in pins:
        check(here / 'inputs/root' / item['path'], item)
        if args.live:
            check(args.root / item['path'], item)
    source = here / 'inputs/root/lean/MicroCFTA'
    def read(name):
        return (source / (name + '.lean')).read_text()
    current = read('SourceCurrentConstrainedCapCurrentNative')
    assert 'Joint annotation state.native.machine.heap state.native' in current
    assert 'Origins state.native.machine.heap state.native' in current
    current_type = current.split('def At ', 1)[1].split('/--', 1)[0]
    assert 'NativeRequestPositivePositions.Support' not in current_type
    native = read('SourceCurrentNativeRequestPositivePositions')
    contract = native.split('theorem call ', 1)[1].split(':= by', 1)[0]
    for token in ['Support source before.native', 'Support source after.native',
                  'History empty before.native.machine.heap', 'Cap Plain depth left',
                  'Cap Plain depth right', 'PositiveAt left path ∨ PositiveAt right path']:
        assert token in contract, token
    rebase = read('SourceCurrentNativePositiveSupportRebase')
    assert 'origins : SourceCurrentConstrainedCapCheckedJointOrigins.Stored source state' in rebase
    assert 'supported : Support source state' in rebase
    assert 'origin.inputs_back' in rebase and 'bindings_back' in rebase
    assert 'theorem Trace.origins' in read('SourceCurrentConstrainedCapCheckedJointOriginTrace')
    for name, token in [('SourceCurrentClassCorridorChronology', 'reads : FoldReads formulas solver actual memos final'),
                        ('SourceCurrentClassObservationSpines', 'reads : NodeReads formulas solver base actual memos final'),
                        ('SourceCurrentSharedEditChildLineage', 'reads : ChildrenReads formulas solver base actual memos final')]:
        assert token in read(name), (name, token)
    owner = read('SourceCurrentOuterSupportedParentHistory').split('def SupportedWritten', 1)[1].split('/--', 1)[0]
    assert 'Support memo' in owner and 'GuardHeap Plain' in owner
    assert 'NativeRequestPositivePositions.Support' not in owner and 'NativeMuPublication.History' not in owner
    capped = read('SourceCurrentCappedProjectionPositivePosition')
    assert 'bounded : Cap Plain capDepth value' in capped.split('theorem root ', 1)[1].split(':= by', 1)[0]
    assert 'bounded : Cap Plain capDepth value' in capped.split('theorem child ', 1)[1].split(':= by', 1)[0]
    observed = read('SourceCurrentClassObservationSpines')
    assert 'Spine formulas solver base (.leaf actual) project read position row true' in observed
    assert '.head (recursive := by assumption)' in observed
    assert 'History start.checked' in read('SourceCurrentSharedEditChildLineage')
    assert '| advance {before : Checked width}' in read('SourceCurrentNativeEdgeWriterGrowth')
    history = read('SourceCurrentNativePublicationTrace')
    assert 'theorem trace ' in history and 'theorem execute ' in history
    geometry = read('SourceCurrentNormalizedChildSeparation')
    assert 'first : Rel classes (index :: left) other' in geometry
    assert 'second : Rel classes (index :: right) other' in geometry
    text = (here / 'plan.md').read_text()
    for token in ['unproved source-only plan', 'zero Lean jobs', 'SAME checked trace',
                  'Trace.origins', 'h0 after.native', 'completed full FoldReads',
                  'no internal Class/Edit/Force/native-query phase', 'PROJECTION RESULT',
                  'full projection INPUT', 'SECOND independent missing local producer',
                  'original false gates', 'same captured warm hit',
                  'TWO derived Rel witnesses', 'global termination', 'Haskell refinement']:
        assert token in text, token
    assert not list(here.glob('*.lean')) and not list(here.glob('*-direct-*.json'))
    assert manifest['scope'] == {'status':'UNPROVED_NEXT_PLAN','lean_jobs':0,'public_pairs':0,'constructed_pairs':0}
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),
                      'root_pins':len(pins),'lean_jobs':0,'public_pairs':0,
                      'constructed_pairs':0,'claim':'UNPROVED_NEXT_PLAN'},sort_keys=True))


if __name__ == '__main__':
    main()
