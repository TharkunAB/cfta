from pathlib import Path
import datetime
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
sha = lambda data: hashlib.sha256(data).hexdigest()
specs = [
    ('20261116-real-eager-captured-output-causal-origin-draft',
     '20261116-real-eager-row-origin-live-root-import-repair',
     'SourcePruningEnumerationRealEagerCapturedOutputOrigin.lean',
     '2d6af45be459a32b2c594b6ef7428d9a89374c30583f523780d091206f02fc51',
     'import', 'row-origin-import-repair'),
    ('20261116-indexed-scan-output-block-origin-draft',
     '20261116-indexed-scan-output-block-default-budget',
     'SourcePruningEnumerationSharedScanOutputBlocks.lean',
     '27799946b14d5c312a84bcac3170cea22ea2844ac3200c7e00557bc4db580b03',
     'default-budget', 'indexed-scan-output-block'),
]
run = base / '20261116-row-import-and-scan-block-default-check'
run.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-row-import-scan-block-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
files = []
imports = set()
jobs = []
selections = []
for original_name, repaired_name, name, digest, change, label in specs:
    original, packet = base / original_name, base / repaired_name
    raw = (original / name).read_bytes()
    assert sha(raw) == digest
    if change == 'import':
        edited = b'import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot\n' + raw
    else:
        option = b'set_option maxHeartbeats 2000000\n'
        assert raw.count(option) == 1
        edited = raw.replace(option, b'')
    packet.mkdir()
    (packet / name).write_bytes(edited)
    for part in ['PUBLIC-HEADER.lean.txt', 'PROBES.lean.txt']:
        (packet / part).write_bytes((original / part).read_bytes())
    assert (packet / 'PUBLIC-HEADER.lean.txt').read_bytes().rstrip() + b' := by' in edited
    repair = {'at': datetime.datetime.now().astimezone().isoformat(), 'status': 'UNCOMPILED',
              'original_packet': original_name, 'original_source_sha256': digest,
              'repaired_source_sha256': sha(edited), 'change': change,
              'header_and_proof_unchanged': True, 'proof_limit': 'default',
              'failed_original_row_check_preserved': change == 'import'}
    (packet / 'REPAIR.json').write_text(json.dumps(repair, indent=2) + '\n')
    manifest = {p.name: sha(p.read_bytes()) for p in packet.iterdir() if p.is_file()}
    (packet / 'MANIFEST.json').write_text(json.dumps({'files': manifest}, indent=2) + '\n')
    source = run / 'source/MicroCFTA' / name
    source.parent.mkdir(parents=True, exist_ok=True)
    probes = (packet / 'PROBES.lean.txt').read_bytes()
    assert probes.count(b'#print axioms ') == 1
    source.write_bytes(edited + b'\n' + probes)
    imports.update(line.split()[1] for line in edited.decode().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((label, command, 1))
    files += [p for p in packet.iterdir() if p.is_file()] + [source]
    selections.append({'packet': repaired_name, 'module': name, 'sha256': sha(edited), 'header_sha256': sha((packet / 'PUBLIC-HEADER.lean.txt').read_bytes())})
jobs.insert(0, ('public-dependencies', 'exec lake build ' + ' '.join(sorted(imports)), 0))
template = (base / '20261116-real-eager-captured-row-origin-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
          and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'actual_indexed_real_eager_row_origin_proved': passed[1], 'indexed_full_scan_block_origin_proved': passed[2],
          'literal_eager_callback_restart_origin_proved': False, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 3 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
(run / 'selection.json').write_text(json.dumps(selections, indent=2) + '\n')
files += list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [Path(__file__), run / 'check.py', run / 'selection.json']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'selections': selections}))
