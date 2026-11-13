#!/usr/bin/env python3
"""Replay source bytes and inspect recorded checks. Do not run Lean or Nix."""
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    manifest = json.loads((BASE / 'manifest.json').read_text())
    for name, entry in manifest['files'].items():
        data = (BASE / name).read_bytes()
        require(SHA(data) == entry['sha256'], 'artifact hash: ' + name)
        require(len(data) == entry['bytes'], 'artifact length: ' + name)
        require(len(data.splitlines()) == entry['lines'], 'artifact lines: ' + name)
    version = subprocess.run(['patch', '--version'], capture_output=True, text=True, check=True)
    require('GNU patch' in version.stdout, 'GNU patch is required')
    restored = {}
    patches = 0
    with tempfile.TemporaryDirectory(prefix='initial-prefix-origin-replay-') as workdir:
        for stage in manifest['stages']:
            name = stage['id']
            if 'base' in stage:
                data = (BASE / stage['base']).read_bytes()
            else:
                target = Path(workdir) / 'current.lean.txt'
                target.write_bytes(restored[stage['from']])
                result = subprocess.run(
                    ['patch', '--batch', '--forward', '--fuzz=0', '--reject-file=-',
                     str(target), str(BASE / stage['patch'])], capture_output=True, text=True,
                    env={**os.environ, 'LC_ALL': 'C'})
                output = result.stdout + result.stderr
                require(result.returncode == 0, 'patch exit: ' + name + ': ' + output)
                require(not re.search(r'\b(offset|fuzz|FAILED|Reversed|previously applied)\b', output, re.I),
                        'patch adjustment: ' + name + ': ' + output)
                data = target.read_bytes()
                patches += 1
            require(SHA(data) == stage['sha256'], 'stage hash: ' + name)
            require(len(data) == stage['bytes'], 'stage length: ' + name)
            require(len(data.splitlines()) == stage['lines'], 'stage lines: ' + name)
            restored[name] = data
    header = (BASE / manifest['header']).read_bytes()
    preamble = (BASE / manifest['preamble']).read_bytes()
    require(len(header.splitlines()) == 48 and SHA(header) ==
            '4e9e9b8c55ab0c419a351e249bb84ed9e844868dc3db34f8aecc095ad1abc00a', 'approved header')
    require(len(preamble.splitlines()) == 14 and SHA(preamble) ==
            'c2117e0be90a1701a17c019aecea74ca427e3e734b2a51dc95598de703d30a2e', 'approved preamble')
    raw_count = 0
    for stage in manifest['stages']:
        if stage['kind'] == 'source':
            text = restored[stage['id']]
            require(text.startswith(preamble), 'unchanged preamble: ' + stage['id'])
            start = text.index(b'private theorem initial_prefix_narrowed_rows')
            stop = text.index(b':= by', start)
            require(text[start:stop].rstrip() + b'\n' == header, 'unchanged header: ' + stage['id'])
            raw_count += 1
    # Validate every preserved draft's original frozen metadata against exact bytes.
    for group in manifest['frozen_metadata']:
        directory = BASE / group['directory']
        for name, entry in json.loads((directory / 'frozen.json').read_text()).items():
            data = restored[group['source_stage']] if name == group['source_basename'] else (directory / name).read_bytes()
            require(SHA(data) == entry['sha256'], 'frozen metadata hash: ' + str(directory / name))
            require(len(data.splitlines()) == entry['lines'], 'frozen metadata lines: ' + name)
    plan = BASE / 'approved-plan'
    for name, entry in json.loads((plan / 'frozen.json').read_text()).items():
        data = (plan / name).read_bytes()
        require(SHA(data) == entry['sha256'] and len(data.splitlines()) == entry['lines'], 'original plan pin: ' + name)
    passed = 0
    final_axioms = []
    for check in manifest['checks']:
        report = json.loads((BASE / check['report']).read_text())
        require(report['compiler_exit'] == check['expected_exit'], 'captured exit: ' + check['id'])
        require(report['sha256'] == SHA(restored[check['input_stage']]), 'captured strict input: ' + check['id'])
        require(report['limits'] == {'memory.max': '4294967296', 'memory.high': '4294967296',
                                     'memory.swap.max': '0'}, 'captured limits: ' + check['id'])
        require(report['public_laws_added'] == 0 and report['emitted_type_origin_proved'] is False,
                'preserved scope metadata: ' + check['id'])
        output = (BASE / check['output']).read_text()
        if check['expected_exit'] == 0:
            groups = [set(word.strip() for word in group.split(',') if word.strip())
                      for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', output, re.S)]
            require(len(groups) == 1 and groups[0] == ALLOWED and 'sorryAx' not in output,
                    'actual successful printed axioms: ' + check['id'])
            final_axioms = sorted(groups[0])
            passed += 1
    require(SHA(restored['checked-final-235']) ==
            '8eba0fbcb07666c58a73cb0df08ef2bdaab1e6af959428fc234ba20dc790861c', 'final raw source')
    require(SHA(restored['check3-strict-input']) ==
            '353eab06125ad7b83eef05fb14262462b58ec6214a2db2ff5727c7685059056b', 'final instrumented input')
    # Check only the archived planning bytes. This is not a type check or a proof.
    planning = manifest['planning_only_entry_preparation']
    require(planning['status'] == 'UNPROVED_NO_BODY_NO_COMPILER_RUN', 'planning-only scope')
    directory = BASE / planning['directory']
    for name, entry in json.loads((directory / 'frozen.json').read_text()).items():
        data = (directory / name).read_bytes()
        require(SHA(data) == entry['sha256'] and len(data.splitlines()) == entry['lines'],
                'unproved plan pin: ' + name)
    result = {'status': 'PASS_SOURCE_REPLAY_ONLY', 'raw_source_stages': raw_count,
              'exact_strict_inputs': len(manifest['checks']), 'all_stages': len(restored),
              'gnu_patches_applied': patches, 'fuzz': 0, 'offsets': 0,
              'artifact_files_verified': len(manifest['files']), 'recorded_strict_passes': passed,
              'recorded_strict_failures': len(manifest['checks']) - passed,
              'actual_final_printed_axioms': final_axioms,
              'final_raw_sha256': SHA(restored['checked-final-235']),
              'final_instrumented_sha256': SHA(restored['check3-strict-input']),
              'public_laws_added': 0, 'Liquid_contracts_checked': False, 'entry_preparation_plan_proved': False,
              'lean_or_nix_run': False, 'live_files_accessed': False}
    if args.report:
        args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
