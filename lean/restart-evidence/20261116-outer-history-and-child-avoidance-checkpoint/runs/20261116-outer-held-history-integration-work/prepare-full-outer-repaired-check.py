from pathlib import Path
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
run = base / '20261116-full-outer-held-history-repaired-check'
run.mkdir()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert hashlib.sha256(owner.read_bytes()).hexdigest() == 'b5ac50c040b628920a02e12766f54a1508f3cc1ff3c9de049648633415cb8331'
parts = [
    ('opaque', '20261116-current-real-opaque-terminal-held-history-outer-match-reduction-repair', '894136bdcf70c3c80be71d4cc211c14c48700cd9503ea89b7f031364cacb542f'),
    ('row', '20261116-current-real-captured-row-held-history-full-context-repair', '6f7e530d6a54603df03cdbc5f540ff612ec91d7cdfbf5e0ad1e9734eb9489f5d'),
    ('scan', '20261116-current-real-prepared-scan-held-history-prefix-name-repair', '1255f5f46897faa333d4ca2d40c133c7e800eb74037c6ead9768569254e24d7c'),
    ('successful', '20261116-current-real-successful-preparation-held-history-local-name-repair', '6030471c067fb55147ce0944eb5fe2295dabc563d7678492fee397400c4aa33f'),
    ('parked', '20261116-current-real-parked-restart-held-history-forecast-opacity-repair', '05699ccf58ab597f6f080bd00670525d910c0288c45597eaa05d18d88f09f7c6'),
    ('right-prefix', '20261116-current-real-right-prefix-prepared-held-history-draft', '48929fb77a9849f76ddd3bf60a179cd9648d7a27c45aa0b151ae9be93ebc5934'),
    ('outer-depth', '20261116-current-real-outer-depth-held-history-opacity-repair', '0532d968e05db25cc1609c216a8f779ec18244cae4306cf9d2d62051034e114a'),
    ('original906', '20261116-current-original-906-held-history-projection-let-repair', '739ccdcf803038a56ebec7648ea450e139d92b4a5106c79598a9eaee5f0475f5'),
]
fragments = {}
files = []
selection = []
for label, folder, digest in parts:
    packet = base / folder
    appendix = packet / 'APPEND.lean.txt'
    assert hashlib.sha256(appendix.read_bytes()).hexdigest() == digest
    fragments[label] = (appendix.read_bytes(), (packet / 'PROBES.lean.txt').read_bytes())
    files += [p for p in packet.iterdir() if p.is_file()]
    selection.append({'label': label, 'folder': folder, 'sha256': digest})
prefix_import = b'import MicroCFTA.SourcePruningEnumerationPrefixHeldHistoryAtOriginalBudget\n'
full = prefix_import + owner.read_bytes() + b'\nsection\nset_option maxHeartbeats 2000000\n'
probes = b''
for label, _, _ in parts:
    full += b'\n' + fragments[label][0]
    probes += b'\n' + fragments[label][1]
full += b'\nend\n'
assert probes.count(b'#print axioms ') == 10
specs = [
    ('opaque-repair', owner.read_bytes() + b'\n' + fragments['opaque'][0], fragments['opaque'][1], 2),
    ('full-outer-chain-and-original906', full, probes, 10),
]
objects = Path(tempfile.mkdtemp(prefix='mcfta-full-outer-held-history-repaired-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = set()
jobs = []
for label, raw, probe, count in specs:
    source = run / 'source' / label / 'MicroCFTA' / owner.name
    source.parent.mkdir(parents=True)
    source.write_bytes(raw + b'\n' + probe)
    files.append(source)
    imports.update(line.split()[1] for line in raw.decode().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    jobs.append((label, command, count))
jobs.insert(0, ('public-dependencies', 'exec lake build ' + ' '.join(sorted(imports)), 0))
template = (base / '20261116-prefix-opaque-and-row-held-history-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == len(jobs)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
          for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'full_outer_candidate_passed': all(passed), 'source_publication_pending': True,
          'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
(run / 'selection.json').write_text(json.dumps(selection, indent=2) + '\n')
files += list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [Path(__file__), run / 'check.py', run / 'selection.json']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'jobs': [(n, c) for n, _, c in jobs]}))
