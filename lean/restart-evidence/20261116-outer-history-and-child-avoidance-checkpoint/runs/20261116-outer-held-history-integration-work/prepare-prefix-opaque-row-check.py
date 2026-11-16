from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-prefix-opaque-and-row-held-history-check'
run.mkdir()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert hashlib.sha256(owner.read_bytes()).hexdigest() == 'b5ac50c040b628920a02e12766f54a1508f3cc1ff3c9de049648633415cb8331'
packets = [
    ('opaque', '20261116-current-real-opaque-terminal-held-history-draft', 'cfcbed9f03d9abbbbd9487498a548eca2d77c272918dce6d263415e9773d7099'),
    ('row', '20261116-current-real-captured-row-held-history-full-context-repair', '6f7e530d6a54603df03cdbc5f540ff612ec91d7cdfbf5e0ad1e9734eb9489f5d'),
    ('scan', '20261116-current-real-prepared-scan-held-history-prefix-name-repair', '1255f5f46897faa333d4ca2d40c133c7e800eb74037c6ead9768569254e24d7c'),
]
fragments = {}
files = []
for label, folder, digest in packets:
    packet = base / folder
    appendix = packet / 'APPEND.lean.txt'
    assert hashlib.sha256(appendix.read_bytes()).hexdigest() == digest
    fragments[label] = (appendix.read_bytes(), (packet / 'PROBES.lean.txt').read_bytes())
    files += [p for p in packet.iterdir() if p.is_file()]

prefix_packet = base / '20261116-current-real-prefix-held-fragment-history-compose-repair'
prefix = prefix_packet / 'SourcePruningEnumerationPrefixHeldHistoryAtOriginalBudget.lean'
assert hashlib.sha256(prefix.read_bytes()).hexdigest() == '5803fed477359f4129cded2294e58b0792c5081a3d08ff39184b0bee961ddb5f'
files += [p for p in prefix_packet.iterdir() if p.is_file()]
specs = [
    ('actual-prefix-history', prefix.name, prefix.read_bytes(), (prefix_packet / 'PROBES.lean.txt').read_bytes(), 1),
    ('opaque-terminal-history', owner.name, owner.read_bytes() + b'\n' + fragments['opaque'][0], fragments['opaque'][1], 2),
    ('captured-row-and-prepared-scan', owner.name,
     owner.read_bytes() + b'\nsection\nset_option maxHeartbeats 2000000\n' + fragments['row'][0] + b'\n' + fragments['scan'][0] + b'\nend\n',
     fragments['row'][1] + b'\n' + fragments['scan'][1], 2),
]
objects = Path(tempfile.mkdtemp(prefix='mcfta-prefix-opaque-row-history-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = set()
jobs = []
assembly = []
for label, name, raw, probes, count in specs:
    source = run / 'source' / label / 'MicroCFTA' / name
    source.parent.mkdir(parents=True)
    assert probes.count(b'#print axioms ') == count
    source.write_bytes(raw + b'\n' + probes)
    files.append(source)
    imports.update(line.split()[1] for line in raw.decode().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((label, command, count))
    assembly.append({'label': label, 'source': str(source.relative_to(root)), 'sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'reports': count})
jobs.insert(0, ('public-dependencies', 'exec lake build ' + ' '.join(sorted(imports)), 0))
template = (base / '20261116-outer-row-scan-and-prefix-history-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
old = "'nonstandard_axioms': bad}"
new = "'nonstandard_axioms': bad, 'diagnostics': len(re.findall(r': error(?:\\(|:)', output)), 'sorryAx': 'sorryAx' in output}"
assert driver.count(old) == 1
driver = driver.replace(old, new)
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == len(jobs)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and c['total_axiom_reports'] == job[2]
          for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'outer_depth_history_proved': False, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
(run / 'assembly.json').write_text(json.dumps(assembly, indent=2) + '\n')
files += list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [Path(__file__), run / 'check.py', run / 'assembly.json']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'jobs': [(n, c) for n, _, c in jobs]}))
