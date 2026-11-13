#!/usr/bin/env python3
"""Reconstruct source stages and validate captured reports without running Lean or Nix."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile

BASE = Path(__file__).resolve().parent
SHA = lambda data: hashlib.sha256(data).hexdigest()
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, detail):
    if not condition:
        raise SystemExit('FAIL: ' + detail)


def axiom_groups(output):
    return [set(x.strip() for x in group.split(',') if x.strip())
            for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    manifest = json.loads((BASE / 'manifest.json').read_text())
    for name, entry in manifest['files'].items():
        data = (BASE / name).read_bytes()
        require(SHA(data) == entry['sha256'], 'artifact hash: ' + name)
        require(len(data) == entry['bytes'] and len(data.splitlines()) == entry['lines'], 'artifact size: ' + name)
    version = subprocess.run(['patch', '--version'], capture_output=True, text=True, check=True)
    require('GNU patch' in version.stdout, 'GNU patch is required')
    restored = {}
    patches = 0
    with tempfile.TemporaryDirectory(prefix='selected-preparation-replay-') as workdir:
        for stage in manifest['stages']:
            name = stage['id']
            if 'base' in stage:
                data = (BASE / stage['base']).read_bytes()
            elif 'same_as' in stage:
                data = restored[stage['same_as']]
            else:
                target = Path(workdir) / 'current.lean.txt'
                target.write_bytes(restored[stage['from']])
                result = subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '--reject-file=-',
                    str(target), str(BASE / stage['patch'])], capture_output=True, text=True,
                    env={**os.environ, 'LC_ALL': 'C'})
                output = result.stdout + result.stderr
                require(result.returncode == 0, 'patch exit: ' + name + ': ' + output)
                require(not re.search(r'\b(offset|fuzz|FAILED|Reversed|previously applied)\b', output, re.I),
                        'patch adjustment: ' + name + ': ' + output)
                data = target.read_bytes()
                patches += 1
            require(SHA(data) == stage['sha256'], 'stage hash: ' + name)
            require(len(data) == stage['bytes'] and len(data.splitlines()) == stage['lines'], 'stage size: ' + name)
            restored[name] = data
    passed = 0
    for check in manifest['checks']:
        report = json.loads((BASE / check['report']).read_text())
        require(report['compiler_exit'] == check['expected_exit'], 'recorded exit: ' + check['id'])
        require(report['sha256'] == SHA(restored[check['input_stage']]), 'exact compiler input: ' + check['id'])
        require(report['limits'] == {'memory.max': '4294967296', 'memory.high': '4294967296',
                                     'memory.swap.max': '0'}, 'recorded limits: ' + check['id'])
        output = (BASE / check['output']).read_text()
        if check['expected_exit'] == 0:
            groups = axiom_groups(output)
            require(bool(groups) and all(group <= ALLOWED for group in groups), 'axiom output: ' + check['id'])
            require('sorryAx' not in output, 'recovery axiom in passed check: ' + check['id'])
            passed += 1
    for number in [2, 3]:
        output = (BASE / f'checks/preparation-check{number}/output.txt').read_text()
        require('error(lean.invalidDottedIdent)' in output, 'retained dotted-identifier diagnostic')
    header = (BASE / 'metadata/mcfta-initial-preparation-origin-body-20261113-1717/header.lean.txt').read_bytes()
    require(len(header.splitlines()) == 52 and SHA(header) ==
        '9e1193a1b98dbdfc0a4bca7948b986738521d1f1d840a7748c9a7aa10656f868', 'approved preparation header')
    for name in ['preparation-failed-395', 'preparation-root-failed-396', 'preparation-failed-394', 'preparation-checked-398']:
        require(header.rstrip() in restored[name], 'unchanged private header: ' + name)
    require(header.replace(b'private theorem', b'theorem', 1).rstrip() in restored['preparation-public-399'],
            'unchanged public preparation statement')
    final = json.loads((BASE / manifest['final_report']).read_text())
    require(len(final['checks']) == 4 and all(c['exit'] == 0 and not c['nonstandard_axioms'] for c in final['checks']),
            'complete passing final publication report')
    for check in final['checks']:
        output = (BASE / 'publication' / (check['name'] + '.txt')).read_text()
        groups = axiom_groups(output)
        require(len(groups) == check['axiom_groups'] and all(group <= ALLOWED for group in groups),
                'final actual axiom output: ' + check['name'])
        require('sorryAx' not in output, 'final recovery axiom: ' + check['name'])
    require(final['reused_checked_sources_unchanged'] == ['prefix236', 'facts101', 'scan_append49'],
            'unchanged strict sources reused without compiler repeats')
    require(final['joint_completion_proved'] is False and final['haskell_changes'] is False, 'scope flags')
    pins_data = (BASE / manifest['final_source_pins']).read_bytes()
    pins = dict(line.split(' ', 1) for line in pins_data.decode().splitlines())
    require(SHA(pins_data) == final['source_tree_sha256'] ==
            '102d5b24ba5d8e9320b0e6fb094a1327fb9f55d771111a2a512a5b669c5a6cbc', 'final source-tree pins')
    require(len(pins) == final['live_modules'] == 5911, 'module count')
    for name, stage in manifest['public_sources'].items():
        require(pins[name] == SHA(restored[stage]), 'public pinned source: ' + name)
    audit = restored['audit-final-strict-input'].decode()
    require(sum(line.startswith('import ') for line in audit.splitlines()) == final['audit_imports'] == 4909, 'Audit imports')
    printed = re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',
                        (BASE / 'publication/final-full-audit-strict.txt').read_text())
    require(printed == ['95033'] and final['audited_theorems'] == 95033, 'Audit theorem count')
    # Preserve the old mathematical target as unproved, and the next visitor as planning only.
    audit_dir = BASE / 'UNPROVED-joint-witness-audit'
    frozen = json.loads((audit_dir / 'frozen.json').read_text())
    for name, info in frozen['files'].items():
        data = (audit_dir / name).read_bytes()
        require(SHA(data) == info['sha256'] and len(data.splitlines()) == info['lines'], 'frozen semantic audit: ' + name)
    visitor = BASE / 'UNPROVED-actual-shared-visitor'
    frozen = json.loads((visitor / 'frozen.json').read_text())
    require(frozen['status'] == 'HEADER_AND_PLAN_ONLY_UNPROVED', 'visitor remains unproved')
    for name, key in [('header.lean.txt', 'header'), ('plan.md', 'plan')]:
        data = (visitor / name).read_bytes()
        require(SHA(data) == frozen[key + '_sha256'] and len(data.splitlines()) == frozen[key + '_lines'], 'visitor pin: ' + name)
    result = {'status': 'PASS_SOURCE_REPLAY_ONLY', 'stages': len(restored), 'gnu_patches_applied': patches,
              'fuzz': 0, 'offsets': 0, 'artifact_files_verified': len(manifest['files']),
              'recorded_focused_calls': len(manifest['checks']), 'recorded_focused_passes': passed,
              'recorded_focused_failures': len(manifest['checks']) - passed, 'recorded_final_calls_passed': 4,
              'recorded_live_modules': 5911, 'recorded_Audit_imports': 4909, 'recorded_theorem_checks': 95033,
              'recorded_source_tree_sha256': final['source_tree_sha256'], 'future_visitor_proved': False,
              'same_output_finite_witness_proved': False, 'lean_or_nix_run': False, 'live_files_accessed': False}
    if args.report:
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
