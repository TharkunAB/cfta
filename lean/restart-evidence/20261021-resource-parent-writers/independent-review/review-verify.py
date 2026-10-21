#!/usr/bin/env python3
"""Verify the independent resource writer review without running Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

SOURCE_SHA = '404f9ba2b58cbdb403608465e375d6f1af66686aaa3201288ba6ea219f75f4d2'
OWNER_SHA = '85c3f13f2e8b2805b11363a28c41d093dcd29f3ae6e476afea3e6a1b42332d84'
NAMESPACE = 'MicroCFTA.SourceCurrentResourceParentWriters.'
KINDS = {'Written': 'def', 'Origins': 'def', 'initial': 'theorem', 'edge_call': 'theorem'}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], str(path)


def public_piece(text: str, kind: str, name: str) -> str:
    start = re.search(r'\b' + kind + r'\s+' + name + r'\b', text).start()
    end = text.find('\n\n', start)
    piece = text[start:end if end >= 0 else len(text)]
    if kind == 'theorem':
        piece = piece.split(' :=', 1)[0]
    return re.sub(r'\s+', '', piece)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / 'review-manifest.json')
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here / relative(pin['path']), pin)
    pins = read(here / 'review-source-pins.json')['files']
    assert pins == manifest['sources']
    for pin in pins:
        snapshot = here / 'inputs/root' / relative(pin['path'])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            assert 1 <= span['start'] <= span['end'] <= len(lines)
            actual = b''.join(lines[span['start']-1:span['end']])
            assert hashlib.sha256(actual).hexdigest() == span['sha256']
        if args.live:
            check(args.root / relative(pin['path']), pin)
    selected = read(here / 'review-selection.json')
    assert selected['finalized'] and selected['source_sha256'] == SOURCE_SHA
    assert selected['public_heads'] == KINDS
    assert selected['new_lean_commands'] == selected['new_lake_commands'] == selected['new_canonical_commands'] == 0
    assert selected['owned_public_pairs'] == selected['constructed_pairs'] == 0
    assert selected['authored_foundations_disclosed'] and not selected['outer_native_stores_transitively_imported']
    assert not selected['official_edits'] and not selected['material_open_findings']
    assert selected['prelaunch_omit_repair_reviewed'] and selected['complete_postlaunch_delta_reviewed']
    assert selected['current_completed_outer_scope_corrected']
    owner = here / 'inputs/owner'
    assert sha(owner / 'resource-writers-manifest.json') == OWNER_SHA == selected['owner_manifest_sha256']
    assert sha(owner / 'resource-writers-selection.json') == selected['owner_selection_sha256']
    command = [sys.executable, str(owner / 'resource-writers-verify.py'), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    author_result = json.loads(subprocess.check_output(command, text=True))
    assert author_result['status'] == 'PASS' and author_result['lean_jobs'] == 3
    assert author_result['failed_checks'] == 1 and author_result['warning_checks'] == 0
    assert author_result['infrastructure_attempts'] == author_result['canonical_jobs'] == author_result['constructed_pairs'] == 0
    assert author_result['public_pairs'] == 4
    source = owner / 'SourceCurrentResourceParentWriters.lean'
    text = source.read_text()
    assert sha(source) == SOURCE_SHA and len(text.splitlines()) == selected['source_lines'] == 250
    assert (here / 'inputs/root/lean/MicroCFTA' / source.name).read_bytes() == source.read_bytes()
    proposed = (owner / 'inputs/plan/proposed-signatures.lean.txt').read_text()
    for name, kind in KINDS.items():
        assert public_piece(text, kind, name) == public_piece(proposed, kind, name), name
    assert re.findall(r'^def (\w+)', text, re.M) == ['Written', 'Origins']
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['initial', 'edge_call']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b', text)
    prelaunch = (owner / 'resource-writers-direct-1.source.lean').read_text()
    expected = prelaunch.replace('(.ready value, running.edgeResults) at observed', '(.ready result, after.edgeResults) at observed').replace(
        'demand_ready_original _ _ value _ observed', 'demand_ready_original _ _ result _ observed').replace(
        'solver owner value := publishedOrigins.checked', 'solver owner result := publishedOrigins.checked').replace(
        'have retained : running.edgeResults.cells handle = some ⟨owner, .returned value⟩',
        'have retained : after.edgeResults.cells handle = some ⟨owner, .returned result⟩').replace(
        'finish_origins handle owner value middleOrigins evaluating written',
        'finish_origins handle owner result middleOrigins evaluating written')
    assert text == expected
    original = (owner / 'resource-writers-source-only.lean').read_text()
    original_body = original.split('private theorem request_eq', 1)[1].split(' := by', 1)[1].split('\n\n', 1)[0]
    prelaunch_body = prelaunch.split('private theorem request_eq', 1)[1].split(' := by', 1)[1].split('\n\n', 1)[0]
    assert original_body == prelaunch_body and 'omit [' not in prelaunch
    assert prelaunch.index('private theorem request_eq') < prelaunch.index('variable [DecidableEq Symbol]')
    ledger = read(owner / 'resource-writers-attempt-ledger.json')['attempts']
    names = [item['name'] for item in ledger]
    assert len(names) == len(set(names)) == selected['copied_owner_lean_commands'] == 3
    assert dict((item['name'], item['exit_code']) for item in ledger) == {
        'resource-writers-direct-1': 1, 'resource-writers-direct-2': 0, 'resource-writers-public-1': 0}
    assert selected['copied_owner_failed_checks'] == 1
    assert selected['copied_owner_warning_checks'] == selected['copied_owner_infrastructure_attempts'] == selected['copied_owner_canonical_commands'] == 0
    assert (owner / (selected['selected_strict'] + '.log')).read_bytes() == b''
    printer = (owner / 'resource-writers-public.lean').read_text()
    assert printer.startswith(text)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    log_path = owner / (selected['selected_public'] + '.log')
    assert log_path.stat().st_size == selected['full_log_bytes'] == 4381684
    assert sha(log_path) == selected['full_log_sha256']
    log = log_path.read_text()
    for name, kind in KINDS.items():
        head = NAMESPACE + name
        checked, printed = log.split('@' + head + ' :', 1)[1].split('\n' + kind + ' ' + head + ' :', 1)
        declared, proof = printed.split(' :=', 1)
        assert ''.join(checked.split()) == ''.join(declared.split()), name
        assert '_private' not in checked + declared
        axiom_match = re.search(re.escape("'" + head + "' depends on axioms:") + r'\s*\[([^\]]*)\]', proof)
        assert axiom_match and len(proof[:axiom_match.start()]) > 500
        actual_axioms = sorted(part.strip() for part in re.sub(r'\.\{[^}]*\}', '', axiom_match.group(1)).split(','))
        assert actual_axioms == selected['axioms_each'] == ['Classical.choice', 'Quot.sound', 'propext']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    written = text.split('def Written ', 1)[1].split('\n\n', 1)[0]
    assert written.count('  ∃ ') == 1
    for clause in ['Context formulas solver inventory writerBefore globals',
                   'Frame formulas solver inventory writerBefore.checked', 'Fits profile writerBefore.checked',
                   'residentReserved bits budget request writerBefore.checked profile',
                   'NativeSupport writerBefore.checked.native.machine.heap writerBefore.checked.native',
                   'Nonempty (History empty writerBefore.checked.native.machine.heap)',
                   'MergeStored writerBefore.merge', 'MergePositive writerBefore.merge']:
        assert clause in written
    report = (here / 'review.md').read_text()
    for phrase in ['zero Lean', 'One historical entry', 'Exact cold publication', 'Exact warm recovery',
                   'canonical inherited', 'event uniqueness', 'ActualParentScanNativeStores',
                   'current baseline already includes', 'unfinished-prefix store extension']:
        assert phrase.lower() in report.lower(), phrase
    clarification = (here / 'inputs/owner-scope-clarification.md').read_text()
    assert 'already includes' in clarification and 'Origins' in clarification
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'new_lean_commands': 0, 'new_lake_commands': 0,
                      'new_canonical_commands': 0, 'reused_owner_lean_commands': 3, 'reused_failed_checks': 1,
                      'reused_warning_checks': 0, 'reused_infrastructure_attempts': 0,
                      'owned_public_pairs': 0, 'copied_public_heads': 4,
                      'public_kinds': KINDS, 'axioms_each': selected['axioms_each'],
                      'manifest_sha256': sha(here / 'review-manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
