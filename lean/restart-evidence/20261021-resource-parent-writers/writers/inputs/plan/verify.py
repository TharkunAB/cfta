#!/usr/bin/env python3
"""Verify the source-only resource Parent writer plan and exact source ranges."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts, value
    return path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'manifest.json').read_text())
    for item in manifest['files']:
        data = (here / relative(item['path'])).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['path']
    pins = json.loads((here / 'source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    ranges = []
    for source in pins['sources']:
        path = relative(source['path'])
        data = (here / relative(source['snapshot'])).read_bytes()
        assert len(data) == source['bytes'] and sha(data) == source['sha256'], str(path)
        lines = data.splitlines(keepends=True)
        for span in source['reviewed_ranges']:
            start, end = span['start'], span['end']
            assert 1 <= start <= end <= len(lines), (str(path), start, end)
            assert sha(b''.join(lines[start-1:end])) == span['sha256']
            ranges.append({'path': str(path), **span})
        if args.live:
            assert sha((args.root / path).read_bytes()) == source['sha256'], str(path)
    assert ranges == json.loads((here / 'ranges.json').read_text())['ranges']
    selection = json.loads((here / 'selection.json').read_text())
    assert selection['finalized'] and not selection['signature_elaborated']
    assert not selection['proposed_result_proved'] and not selection['official_edits']
    assert not selection['implementation_authorized_in_this_package']
    assert selection['proposed_public_heads'] == [
        'SourceCurrentResourceParentWriters.Written', 'SourceCurrentResourceParentWriters.Origins',
        'SourceCurrentResourceParentWriters.initial', 'SourceCurrentResourceParentWriters.edge_call']
    for field in ('new_lean_commands', 'new_lake_commands', 'new_canonical_commands',
                  'new_public_pairs', 'new_constructed_pairs'):
        assert pins[field] == selection[field] == 0
    text = (here / 'proposed-signatures.lean.txt').read_text()
    assert text.count('def Written ') == text.count('def Origins ') == 1
    assert text.count('theorem initial ') == text.count('theorem edge_call') == 1
    written = text.split('def Written ', 1)[1].split('-- The exact cell.request', 1)[0]
    assert written.count('  ∃ ') == 1
    for clause in ('writerBefore : Caller (bits + 2)', '(globals : Memos)',
                   'Context formulas solver inventory writerBefore globals',
                   'Frame formulas solver inventory writerBefore.checked',
                   'Fits profile writerBefore.checked', 'EqReady writerBefore.checked.operations.constraints request.inherited',
                   'EdgeResident writerBefore.checked.native.machine.heap request.value',
                   'FieldAvailable writerBefore.checked.operations request.value.entry.key.constraint',
                   'residentReserved bits budget request writerBefore.checked profile',
                   'Normal writerBefore.checked.native.machine.heap',
                   'NativeSupport writerBefore.checked.native.machine.heap writerBefore.checked.native',
                   'Nonempty (History empty writerBefore.checked.native.machine.heap)',
                   'MergeStored writerBefore.merge', 'MergePositive writerBefore.merge'):
        assert clause in written, clause
    assert 'SupportedWritten' not in written
    assert 'FlatMemoThunk.CellSpec (Written (bits := bits) formulas solver)' in text
    edge = text.split('theorem edge_call', 1)[1]
    for clause in ('(context : Context', '(frame : Frame', '(fits : Fits', '(inherited : EqReady',
                   '(resident : EdgeResident', '(reserved : SourceCurrentEdgeCallNumeric.Reserved',
                   '(origins : Origins', '(normal : Normal', '(supported : NativeSupport',
                   '(causal : History', '(merged : MergeStored', '(positiveMemo : MergePositive',
                   'Origins formulas solver after ∧ Written (bits := bits) formulas solver request result'):
        assert clause in edge, clause
    for forbidden in ('(ranges :', '(current :', '(required :', '(passReads :', 'theorem reached'):
        assert forbidden not in text, forbidden
    plan = (here / 'plan.md').read_text()
    for clause in ('SOURCE-ONLY PLAN', 'ONE existential tuple', 'demand_spec', 'finish_spec',
                   'unpacks its Written ONCE', 'Path-list equality is not record equality',
                   'complete captured request equals the candidate', 'missing extension is the NEW four-law', 'OuterInitialPrefix.reached', 'It has no supplied Back, common-anchor, fixed-point, or Covers oracle',
                   'No later reader may imply past writer resources', 'not compiled Lean'):
        assert clause in plan, clause
    old = here / 'inputs/authority/old-writer-plan.md'
    assert sha(old.read_bytes()) == selection['old_writer_plan_sha256']
    frozen = next(s for s in pins['sources'] if s['path'].endswith('/SourceCurrentOuterSupportedParentHistory.lean'))
    assert frozen['sha256'] == selection['old_551_ledger_sha256']
    assert len((here / frozen['snapshot']).read_text().splitlines()) == 551
    print(json.dumps({'status': 'PASS', 'live': args.live, 'root_sources': len(pins['sources']),
                      'reviewed_ranges': len(ranges), 'pins': len(manifest['files']) + len(manifest['sources']),
                      'new_lean_commands': 0, 'new_lake_commands': 0, 'new_canonical_commands': 0,
                      'new_public_pairs': 0, 'new_constructed_pairs': 0,
                      'proposal_proved': False, 'signature_elaborated': False,
                      'manifest_sha256': sha((here / 'manifest.json').read_bytes())}, indent=2))


if __name__ == '__main__':
    main()
