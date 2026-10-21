#!/usr/bin/env python3
"""Check the completed-Scan store plan and its exact source snapshots."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'manifest.json').read_text())
    for item in manifest['files']:
        rel = Path(item['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        data = (here / rel).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], str(rel)
    pins = json.loads((here / 'source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    ranges = []
    for item in pins['sources']:
        rel, snapshot = Path(item['path']), Path(item['snapshot'])
        assert not rel.is_absolute() and '..' not in rel.parts
        assert not snapshot.is_absolute() and '..' not in snapshot.parts
        data = (here / snapshot).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], str(rel)
        lines = data.splitlines(keepends=True)
        for span in item['reviewed_ranges']:
            start, end = span['start'], span['end']
            assert 1 <= start <= end <= len(lines)
            assert sha(b''.join(lines[start-1:end])) == span['sha256']
            ranges.append({'path': item['path'], **span})
        if args.live:
            assert sha((args.root / rel).read_bytes()) == item['sha256'], str(rel)
    dependency = pins['next_dependency']
    data = (here / dependency['snapshot']).read_bytes()
    assert len(data) == dependency['bytes'] and sha(data) == dependency['sha256']
    assert dependency['sha256'] == '924446496dd6d5fe0032bd703411d0dbdb5d5595e904d56516a2cb422e18f6da'
    assert len(data.splitlines()) == 78
    indexed = json.loads((here / 'ranges.json').read_text())
    assert indexed['ranges'] == ranges
    assert indexed['next_ranges'] == [{'path': dependency['snapshot'], **span} for span in dependency['reviewed_ranges']]
    selection = json.loads((here / 'selection.json').read_text())
    assert selection['finalized'] and not selection['proposed_result_proved']
    assert not selection['implementation_authorized_in_this_package'] and not selection['official_edits']
    assert selection['proposed_public_heads'] == ['SourceCurrentScanNativeStores.scan']
    assert selection['completed_graph_only'] and selection['initial_scoped_and_idle_required']
    assert selection['initial_current_support_history_required']
    for flag in ['root_caps_required', 'caller_ranges_required', 'memo_correct_required', 'worker_to_physical_admission_solved']:
        assert not selection[flag]
    for key in ['new_lean_commands', 'new_canonical_commands', 'new_public_pairs', 'new_constructed_pairs']:
        assert selection[key] == pins[key] == 0
    assert not any(item['path'].endswith('/SourceCurrentNativeRequestPositivePositions.lean') for item in pins['sources'])
    plan = (here / 'plan.md').read_text()
    for phrase in ['SOURCE-ONLY PLAN', 'the proposed Scan theorem is unproved', 'same completed', 'No input cap or whole-forest closure', 'NOT SourceEqualityAnnotationHeap.Heap Plain', 'does not derive physical admission from an execute.done', 'No semantic Memo.Correct', 'historical Parent writer entry']:
        assert phrase.lower() in plan.lower(), phrase
    signature = (here / 'proposed-signature.lean.txt').read_text()
    assert signature.count('theorem scan') == 1
    for term in ['(actual : Scan', '(ready : Ready before)', '(proper :', '(current :', '(supported :', '(causal :', 'Ready after', 'Nonempty (History empty after.native.machine.heap)']:
        assert term in signature, term
    assert 'Cap Plain' not in signature and 'Ranges' not in signature and 'Memo.Correct' not in signature
    print(json.dumps({'status': 'PASS', 'live': args.live, 'root_sources': len(pins['sources']), 'next_here_sources': 1, 'reviewed_ranges': len(ranges)+1, 'pins': len(manifest['files'])+len(manifest['sources']), 'new_lean_commands': 0, 'new_canonical_commands': 0, 'new_public_pairs': 0, 'new_constructed_pairs': 0, 'proposed_result_proved': False, 'manifest_sha256': sha((here/'manifest.json').read_bytes())}, indent=2))


if __name__ == '__main__':
    main()
