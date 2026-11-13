from pathlib import Path
import argparse
import hashlib
import json
import re

packet = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description='Reconstruct source text without Lean, GNU patch, Git, or subprocesses.')
parser.add_argument('--extract', type=Path)
parser.add_argument('--check-imports', type=Path, metavar='REPOSITORY')
args = parser.parse_args()
manifest = json.loads((packet / 'source-history.json').read_text())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(entry):
    data = (packet / entry['file']).read_bytes()
    assert digest(data) == entry['sha256'], entry['file']
    return data


def apply_zero(before, patch):
    original = before.decode().splitlines(True)
    changes = patch.decode().splitlines(True)
    assert changes[0].startswith('--- ') and changes[1].startswith('+++ ')
    output, cursor, at = [], 0, 2
    while at < len(changes):
        found = re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@\n', changes[at])
        assert found, changes[at]
        old_start, old_count, new_start, new_count = [int(x) if x is not None else 1 for x in found.groups()]
        start = old_start if old_count == 0 else old_start - 1
        assert cursor <= start <= len(original)
        output.extend(original[cursor:start])
        assert len(output) == (new_start if new_count == 0 else new_start - 1)
        deleted, inserted = [], []
        at += 1
        while at < len(changes) and not changes[at].startswith('@@ '):
            line = changes[at]
            assert line[0] in '+-', 'Context lines are forbidden'
            (inserted if line[0] == '+' else deleted).append(line[1:])
            at += 1
        assert len(deleted) == old_count and len(inserted) == new_count
        assert original[start:start + old_count] == deleted
        output.extend(inserted)
        cursor = start + old_count
    output.extend(original[cursor:])
    return ''.join(output).encode()


stages, replays = {}, 0
for family in manifest['families']:
    data = read(family['base'])
    stages[family['base']['name']] = data
    for stage in family['stages']:
        change = (packet / stage['patch']).read_bytes()
        assert digest(change) == stage['patch_sha256']
        data = apply_zero(data, change)
        assert digest(data) == stage['sha256'], stage['name']
        stages[stage['name']] = data
        replays += 1
assert len(stages) == manifest['expected_source_stages']
assert replays == manifest['expected_zero_context_replays']
header = read(manifest['header'])
assert apply_zero(b'', read(manifest['header']['patch_from_empty'])) == header
preamble = read(manifest['preamble'])
for data in stages.values():
    assert data.count(header.rstrip()) == 1 and data.startswith(preamble)
for entry in manifest['frozen_artifacts']:
    read(entry)
read(manifest['root_checker'])
for number, diagnostic in enumerate(manifest['diagnostics'], 1):
    data = stages[diagnostic['stage']]
    assert digest(data) == diagnostic['source_sha256']
    instrumented = apply_zero(data, read(diagnostic['instrumentation']))
    assert digest(instrumented) == diagnostic['instrumented_sha256']
    files = {Path(entry['file']).name: read(entry) for entry in diagnostic['files']}
    report = json.loads(files['draft-checked.json'])
    assert report['sha256'] == digest(instrumented)
    assert report['compiler_exit'] == diagnostic['compiler_exit']
    assert report['limits'] == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    if diagnostic['compiler_exit'] == 0:
        printed = re.findall(r'depends on axioms:\s*\[([^]]*)\]', files['draft-output.txt'].decode(), re.S)
        assert len(printed) == 1
        actual = {name.strip() for name in printed[0].split(',')}
        assert actual == {'propext', 'Classical.choice', 'Quot.sound'}
    if args.extract:
        args.extract.mkdir(parents=True, exist_ok=True)
        (args.extract / f'check{number}.lean').write_bytes(instrumented)
if args.extract:
    for name, data in stages.items():
        (args.extract / f'{name}.lean').write_bytes(data)
if args.check_imports:
    final = stages['compiled-witnesses-122'].decode()
    for module in re.findall(r'^import ([A-Za-z0-9_.]+)$', final, re.M):
        assert (args.check_imports / 'lean' / Path(module.replace('.', '/')).with_suffix('.lean')).is_file(), module
print(json.dumps({'source_stages': len(stages), 'source_transitions': replays,
                  'instrumented_stages': len(manifest['diagnostics']), 'header_replays': 1,
                  'reconstruction': 'PURE_TEXT_EXACT', 'gnu_patch_run': False, 'compiler_run': False,
                  'stored_root_final_compiler_exit': 0, 'public_laws_added': 0}))
