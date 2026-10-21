#!/usr/bin/env python3
"""Verify the portable source-only older-owner lineage plan."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'plan-manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        data = (HERE / item['path']).read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert digest(data) == item['sha256'], item['path']
    sources = json.loads((HERE / 'sourcepins.json').read_text())['pins']
    range_count = 0
    for item in sources:
        data = (HERE / item['snapshot']).read_bytes()
        assert digest(data) == item['sha256'], item['snapshot']
        if args.live:
            live = (args.root / item['root_path']).read_bytes()
            assert digest(live) == item['sha256'], item['root_path']
        lines = data.splitlines(keepends=True)
        for interval in item['reviewed_ranges']:
            actual = b''.join(lines[interval['first'] - 1:interval['last']])
            assert actual == (HERE / interval['snapshot']).read_bytes(), interval['snapshot']
            assert digest(actual) == interval['sha256'], interval['snapshot']
            range_count += 1
    status = json.loads((HERE / 'status.json').read_text())
    for key in ['compiler_jobs', 'runtime_jobs', 'canonical_jobs', 'new_theorems', 'counterexample_executions']:
        assert status[key] == 0, key
    assert status['pure_count_theorem'] == 'unproved'
    assert status['graph_rank_theorem'] == 'unproved later target'
    assert status['actual_back_producer'] == 'unproved separate required_memos plan'
    select = json.loads((HERE / 'selection.json').read_text())
    assert select['source_reviewed'] and not select['elaborated']
    assert not select['implementation_authorized_by_this_package']
    geometry = (HERE / 'proposed-geometry-signatures.lean.txt').read_text()
    assert geometry.count('noncomputable def count ') == 1
    assert geometry.count('theorem child_count\n') == 1
    assert digest(geometry.encode()) == select['geometry_signature_sha256']
    graph = (HERE / 'proposed-graph-contract.lean.txt').read_text()
    assert graph.count('theorem body_rank_lt\n') == 1
    assert digest(graph.encode()) == select['later_graph_signature_sha256']
    plan = (HERE / 'plan.md').read_text()
    assert 'Fixed/live C separates' not in plan
    assert 'Fixed C separates' in plan
    old = (HERE / 'plan-before-fixed-wording.md').read_text()
    assert old.replace('Fixed/live C separates', 'Fixed C separates') == plan
    owner = (HERE / 'sourcepins/SourceCurrentPositiveOwnerPair.lean').read_bytes().splitlines(keepends=True)
    separation = (HERE / 'sourcepins/SourceCurrentPositiveInheritedChildSeparation.lean').read_bytes().splitlines(keepends=True)
    assert owner[22:74] == separation[22:74]
    print(json.dumps({'status': 'PASS', 'live': args.live, 'source_only': True,
        'local_pins': len(manifest['files']), 'root_pins': len(sources),
        'reviewed_ranges': range_count, 'compiler_jobs': 0, 'runtime_jobs': 0,
        'new_theorems': 0, 'pure_count_and_lineage_unproved': True,
        'actual_back_producer_open': True, 'copied_enumeration_lines': 52,
        'authored_foundations_disclosed': True,
        'manifest_sha256': digest((HERE / 'plan-manifest.json').read_bytes())}, indent=2))

if __name__ == '__main__':
    main()
