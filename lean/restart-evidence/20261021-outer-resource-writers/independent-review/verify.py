#!/usr/bin/env python3
"""Verify the independent review of resource writer transport through actual outer prefixes."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentOuterResourceWriters.lean'
HEAD = 'MicroCFTA.SourceCurrentOuterResourceWriters.reached'
PREFIX = 'outer-resource-writers-'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256'], str(path)


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts, value
    return path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    selected = json.loads((HERE / 'selection.json').read_text())
    assert manifest['finalized'] and manifest['independent_review'] and selected['finalized']
    assert manifest['owned_lean_lake_commands'] == manifest['owned_public_pairs'] == 0
    for pin in manifest['files']:
        check(HERE / relative(pin['path']), pin)
    pins = json.loads((HERE / 'source-pins.json').read_text())['sources']
    assert pins == manifest['sources']
    for pin in pins:
        snapshot = HERE / relative(pin['snapshot'])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo, hi = span['start'], span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert sha(b''.join(lines[lo-1:hi])) == span['sha256']
        if args.live:
            check(args.root / relative(pin['path']), pin)
    owner = HERE / 'inputs/owner'
    source = (owner / SOURCE).read_text()
    assert sha(source.encode()) == selected['final_source_sha256']
    assert len(source.splitlines()) == selected['final_source_lines']
    if args.live:
        assert sha((args.root / 'lean/MicroCFTA' / SOURCE).read_bytes()) == selected['final_source_sha256']
    assert re.findall(r'^theorem (\w+)', source, re.M) == ['reached']
    assert not re.search(r'\b(?:sorry|axiom|admit|native_decide|trustCompiler)\b|_private', source)
    public = source.split('theorem reached', 1)[1].split(' := by', 1)[0].strip()
    proposal = (HERE / 'inputs/plan/proposed-signature.lean.txt').read_text()
    proposal = proposal.split('theorem reached', 1)[1].split('\nend MicroCFTA.', 1)[0].strip()
    assert public == proposal
    assert 'SourceCurrentOuterExecutionAncestry (Step Reached)' in source
    assert '(actual : Reached g s r e p h m c n budget first last)' in public
    assert 'SourceCurrentOuterActiveAncestry.Reached' not in source
    assert source.count('SourceCurrentResourceParentWriters.edge_call') == 1
    assert source.count('SourceCurrentOuterEdgeGuardAlphabet.edge_call') == 1
    assert source.count('SourceCurrentOuterNativeStores.edge_call') == 1
    assert source.count('SourceCurrentOuterNativeStores.descendants') == 1
    assert source.count('SourceCurrentOuterNativeStores.node_call') == 1
    assert source.count('SourceCurrentOuterPrefixNativeStores.reached formulas solver seed earlier') == 1
    assert source.count('change Origins formulas solver middle') == 2
    assert re.findall(r'^private def (NodeCallAt|NodeBodyAt|RowsAt|DescendantsAt|ChildrenAt|WalkAt)', source, re.M) == [
        'NodeCallAt', 'NodeBodyAt', 'RowsAt', 'DescendantsAt', 'ChildrenAt', 'WalkAt']
    assert 'parentSeed receipt.post.context receipt.frame' in source
    assert '(Schedule.node fuel budget seed) headPost.context' in source
    assert sha((HERE / 'inputs/prelaunch' / SOURCE).read_bytes()) == 'e4e88ee9d08656f1eb92151de30e31d4f01634a20e950ed8dba719e54d3eaaf9'
    assert json.loads((HERE / 'prelaunch-type-comparison.json').read_text())['elaboration_claimed'] is False
    owner_selection = json.loads((owner / (PREFIX + 'selection.json')).read_text())
    assert sha((owner / (PREFIX + 'manifest.json')).read_bytes()) == selected['owner_manifest_sha256']
    strict = owner_selection['selected_strict']
    assert not (owner / (strict + '.log')).read_bytes()
    assert (owner / (strict + '.source.lean')).read_text() == source
    public_stem = owner_selection['selected_public']
    printer = (owner / (public_stem + '.source.lean')).read_text()
    assert printer.startswith(source)
    for option in ('linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000'):
        assert printer.count('set_option ' + option) == 1
    for directive in ('#check @', '#print ', '#print axioms '):
        assert printer.count(directive + HEAD) == 1
    data = (owner / (public_stem + '.log')).read_bytes()
    assert len(data) == selected['public_log_bytes'] and sha(data) == selected['public_log_sha256']
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked, printed = log.split('@' + HEAD + ' :', 1)[1].split('\ntheorem ' + HEAD + ' :', 1)
    declared, proof = printed.split(' :=', 1)
    assert ''.join(checked.split()) == ''.join(declared.split()) and '_private' not in checked + declared
    report = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r'\s*\[([^\]]*)\]', proof)
    assert report and len(proof[:report.start()]) > 1000
    assert {re.sub(r'\.\{[^}]*\}', '', x.strip()) for x in report.group(1).split(',')} == {
        'propext', 'Classical.choice', 'Quot.sound'}
    command = [sys.executable, str(owner / (PREFIX + 'verify.py')), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    result = subprocess.run(command, cwd='/', env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                            capture_output=True, text=True)
    assert result.returncode == 0, (result.stdout, result.stderr)
    owner_result = json.loads(result.stdout)
    assert owner_result['status'] == 'PASS'
    print(json.dumps({'status': 'PASS', 'live': args.live, 'independent_review': True,
                      'material_open_issues': 0, 'local_pins': len(manifest['files']), 'root_pins': len(pins),
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'reused_lean_jobs': selected['reused_lean_jobs'], 'reused_failures': selected['reused_failures'],
                      'reused_canonical_jobs': 0, 'reused_public_pairs': 1, 'public_type_identity': True,
                      'all_eight_printer_settings': True, 'standard_axioms_only': True,
                      'selected_source_live_checked': args.live,
                      'authored_dependencies_disclosed': True,
                      'manifest_sha256': sha((HERE / 'manifest.json').read_bytes()),
                      'frozen_owner_checker': owner_result}, indent=2))


if __name__ == '__main__':
    main()
