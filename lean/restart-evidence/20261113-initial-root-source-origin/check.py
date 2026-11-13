#!/usr/bin/env python3
"""Replay the recorded source patches. This command does not run Lean or Nix."""
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


def groups(output):
    return [set(word.strip() for word in group.split(',') if word.strip())
            for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, help='Write the replay report here.')
    args = parser.parse_args()
    manifest = json.loads((BASE / 'manifest.json').read_text())
    artifact_bytes = 0
    for name, entry in manifest['files'].items():
        data = (BASE / name).read_bytes()
        require(SHA(data) == entry['sha256'], 'artifact hash: ' + name)
        require(len(data) == entry['bytes'], 'artifact length: ' + name)
        require(len(data.splitlines()) == entry['lines'], 'artifact lines: ' + name)
        artifact_bytes += len(data)
    patch_version = subprocess.run(['patch', '--version'], capture_output=True, text=True, check=True)
    require('GNU patch' in patch_version.stdout, 'GNU patch is required')
    restored = {}
    patch_count = 0
    with tempfile.TemporaryDirectory(prefix='initial-root-source-replay-') as workdir:
        for entry in manifest['stages']:
            name = entry['id']
            if 'base' in entry:
                data = (BASE / entry['base']).read_bytes()
            elif 'same_as' in entry:
                data = restored[entry['same_as']]
            else:
                target = Path(workdir) / 'current.lean.txt'
                target.write_bytes(restored[entry['from']])
                result = subprocess.run(
                    ['patch', '--batch', '--forward', '--fuzz=0', '--reject-file=-',
                     str(target), str(BASE / entry['patch'])],
                    capture_output=True, text=True, env={**os.environ, 'LC_ALL': 'C'})
                output = result.stdout + result.stderr
                require(result.returncode == 0, 'patch exit for ' + name + ': ' + output)
                require(not re.search(r'\b(offset|fuzz|FAILED|Reversed|previously applied)\b', output, re.I),
                        'patch needs an offset or fuzz: ' + name + ': ' + output)
                data = target.read_bytes()
                patch_count += 1
            require(SHA(data) == entry['sha256'], 'stage hash: ' + name)
            require(len(data) == entry['bytes'], 'stage length: ' + name)
            require(len(data.splitlines()) == entry['lines'], 'stage lines: ' + name)
            restored[name] = data
    passed_private = 0
    for check in manifest['checks']:
        report = json.loads((BASE / check['report']).read_text())
        require(report['compiler_exit'] == check['expected_exit'], 'recorded exit: ' + check['id'])
        require(report['sha256'] == SHA(restored[check['input_stage']]), 'strict input hash: ' + check['id'])
        require(report['limits'] == {'memory.max': '4294967296', 'memory.high': '4294967296',
                                     'memory.swap.max': '0'}, 'recorded limits: ' + check['id'])
        output = (BASE / check['output']).read_text()
        if check['expected_exit'] == 0:
            actual_groups = groups(output)
            require(bool(actual_groups), 'missing axiom report: ' + check['id'])
            require('sorryAx' not in output, 'unexpected recovery axiom: ' + check['id'])
            require(all(group <= ALLOWED for group in actual_groups), 'nonstandard axiom: ' + check['id'])
            passed_private += 1
    pins_data = (BASE / manifest['public_source_pins']).read_bytes()
    pins = dict(line.split(' ', 1) for line in pins_data.decode().splitlines())
    final = json.loads((BASE / manifest['public_final_report']).read_text())
    require(SHA(pins_data) == final['source_tree_sha256'], 'public source-tree hash')
    require(len(pins) == final['live_modules'] == 5906, 'public module count')
    for filename, name in manifest['public_sources'].items():
        require(pins[filename] == SHA(restored[name]), 'public source pin: ' + filename)
    audit = restored['audit-final-strict-input'].decode()
    require(sum(line.startswith('import ') for line in audit.splitlines()) == final['audit_imports'] == 4904,
            'Audit import count')
    require(final['audited_theorems'] == 94990, 'Audit theorem count')
    require(final['namespace_instrumentation_repaired'] is True, 'namespace repair flag')
    require(final['joint_completion_proved'] is False, 'semantic scope flag')
    require(final['passed_checks_repeated'] is False, 'passed checks were retained')
    require(len(final['checks']) == 7, 'seven final public checks')
    for check in final['checks']:
        require(check['exit'] == 0 and not check['nonstandard_axioms'], 'final public check: ' + check['name'])
        directory = 'full-public' if check['name'] in [
            'full-audit-build', 'SourceSynthesisCurrentCandidateAppOperands-strict',
            'SourceSynthesisCurrentInitialOuterNarrowRows-strict'] else 'namespace-repair'
        output = (BASE / 'publication' / directory / (check['name'] + '.txt')).read_text()
        actual_groups = groups(output)
        require(len(actual_groups) == check['axiom_groups'], 'public axiom group count: ' + check['name'])
        require('sorryAx' not in output and all(group <= ALLOWED for group in actual_groups),
                'public axiom report: ' + check['name'])
    failed = json.loads((BASE / manifest['public_failed_report']).read_text())
    require(len(failed) == 4 and failed[-1]['exit'] == 1 and all(x['exit'] == 0 for x in failed[:-1]),
            'original public namespace-instrumentation failure')
    require(failed[:3] == final['checks'][:3], 'same completed public checks retained')
    print_counts = re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',
        (BASE / 'publication/namespace-repair/full-audit-strict.txt').read_text())
    require(print_counts == ['94990'], 'captured strict Audit count')
    # The audits retain their original self-pins; the plan remains unproved.
    for name in ['shared-scope-correction', 'PLANNING-ONLY-prefix-origin']:
        directory = BASE / 'audits' / name
        for filename, expected in json.loads((directory / 'frozen.json').read_text()).items():
            data = (directory / filename).read_bytes()
            require(SHA(data) == expected['sha256'], 'frozen audit hash: ' + name + '/' + filename)
            require(len(data.splitlines()) == expected['lines'], 'frozen audit lines: ' + filename)
    result = {'status': 'PASS_SOURCE_REPLAY_ONLY', 'stages': len(restored), 'gnu_patches_applied': patch_count,
              'fuzz': 0, 'offsets': 0, 'artifacts_verified': len(manifest['files']),
              'artifact_bytes_verified': artifact_bytes, 'recorded_focused_checks': len(manifest['checks']),
              'recorded_focused_passes': passed_private,
              'recorded_public_checks_passed': 7, 'recorded_public_modules': 5906,
              'recorded_Audit_imports': 4904, 'recorded_Audit_theorems': 94990,
              'recorded_source_tree_sha256': final['source_tree_sha256'],
              'lean_or_nix_run': False, 'live_files_accessed': False,
              'new_semantic_theorems_or_eager_provenance_claims': False}
    if args.report:
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
