from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
CONTROL = BASE / '20261118-incoming-query-seeds-check-control-draft'
WORK = BASE / '20261118-terminal-query-resources-work'
assert Path(__file__).resolve().parent == WORK.resolve(), 'Root copies this NEW preparer into the SAME Work60 directory.'
assert Path(__file__).read_bytes() == (CONTROL / 'prepare-incoming-seeds-check.py').read_bytes()
selection = json.loads((CONTROL / 'SELECTION.json').read_text())
runtime = BASE / selection['runtime']
assert not runtime.exists(), 'Use a new runtime and preserve every prior attempt.'
SHA = lambda data: hashlib.sha256(data).hexdigest()
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record, dict) else record), str(path)
    if isinstance(record, dict) and 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    bound.add(path)
    return data


def records(manifest):
    files = manifest['files']
    return files.items() if isinstance(files, dict) else [(item.get('file', item.get('path')), item) for item in files]


for name, record in records(json.loads((CONTROL / 'MANIFEST.json').read_text())):
    verify(CONTROL / name, record)
bound.add(CONTROL / 'MANIFEST.json')
for name, record in json.loads((CONTROL / 'RECEIPT-PINS.json').read_text()).items():
    verify(ROOT / name, record)
assert selection['source_commit'] == '04e2eb843816747cab7ec59a150d0897619274b4'
assert selection['source_files'] == 6283
assert selection['expected_checks'] == len(selection['components']) == 1
assert selection['expected_public_axiom_reports'] == 1
assert selection['expected_explicit_private_axiom_reports'] == selection['expected_declaration_checks'] == 0
assert selection['new_private_helpers_transitive'] == 2 and selection['new_definitions'] == 0
assert selection['prior_checkpoint_push_required_for_private_check']
assert selection['prior_checkpoint_push_required_before_normal_Source_staging']
assert selection['prior_checkpoint_commit_is_dynamic']
prior = BASE / selection['prior_work']
publication = BASE / selection['prior_publication_runtime']
commit = json.loads((prior / 'SOURCE-COMMIT.json').read_text())
receipt = json.loads((prior / 'PUBLICATION-VERIFIED.json').read_text())
actual = json.loads((prior / 'PUBLICATION-ACTUAL-RUN.json').read_text())
checked = json.loads((publication / 'checked.json').read_text())
assert commit['source_commit'] == selection['source_commit'] and commit['actual_terminal'] and commit['actual_terminal_exit'] == 0
assert commit['publication_actual_session'] == receipt['actual_session'] == actual['actual_session'] == 72663
assert receipt['actual_terminal'] and actual['actual_terminal']
assert receipt['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
assert checked == json.loads((publication / 'results.json').read_text()) and checked['checks'] == receipt['checks']
assert SHA((publication / 'checked.json').read_bytes()) == receipt['checked_sha256']
assert SHA((publication / 'source-pins.json').read_bytes()) == receipt['source_pins_sha256']
assert [item['total_axiom_reports'] for item in checked['checks']] == [735, 2, 330, 735, 735]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms']
    and item['declaration_checks'] == 0 for item in checked['checks'])
assert checked['all_five_gates_passed'] and checked['source_pins_unchanged']
assert receipt['source_files'] == 6283 and receipt['direct_audit_imports'] == 5283
assert receipt['audited_theorems'] == commit['audited_theorems'] == 100218
assert receipt['pins_independently_reverified'] == 8398
assert not receipt['joint_finite_completion_proved']
assert len(json.loads((publication / 'source-pins.json').read_text())) == 8398
for name, digest in json.loads((publication / 'source-pins.json').read_text()).items():
    verify(ROOT / name, digest)
commit_actual = json.loads((prior / 'SOURCE-COMMIT-ACTUAL-RUN.json').read_text())
assert commit_actual['actual_session'] == 22154 and commit_actual['actual_terminal'] and commit_actual['actual_terminal_exit'] == 0
assert commit_actual['source_commit'] == commit['source_commit'] == selection['source_commit']
assert commit_actual['parent'] == commit['parent'] == '6546febba4473d4347d8e4d4c68ea1c90cb7dae3'
assert commit_actual['source_payload_files'] == len(commit['files']) == 2
assert set(commit['files']) == {'lean/MicroCFTA/SourcePruningEnumerationSharedTerminalFoldQueryEvents.lean', 'lean/MicroCFTA/Audit.lean'}
# Documentation and frozen evidence may advance HEAD after this Source commit.
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', selection['source_commit'], 'HEAD'], cwd=ROOT, check=True)
changes = subprocess.check_output(['git', 'diff', '--name-only', selection['source_commit'], 'HEAD'], cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md'] or name.startswith('lean/restart-evidence/') for name in changes), changes
subprocess.run(['git', 'diff', '--quiet', selection['source_commit'], 'HEAD', '--',
    'lean/MicroCFTA', 'lean/lake-manifest.json', 'lean/lakefile.toml', 'lean/lean-toolchain', 'shell.nix'], cwd=ROOT, check=True)
baseline = json.loads((CONTROL / selection['source_baseline']).read_text())
assert baseline['source_commit'] == selection['source_commit'] and baseline['source_files'] == 6283
sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
assert {str(path.relative_to(ROOT)) for path in sources} == set(baseline['sources']) and len(sources) == 6283
public_pins = json.loads((publication / 'source-pins.json').read_text())
for name, record in {**baseline['sources'], **baseline['toolchain']}.items():
    verify(ROOT / name, record)
    assert public_pins[name] == record['sha256'], name
push = json.loads((ROOT / selection['prior_push_verified_receipt']).read_text())
assert push['source_commit'] == selection['source_commit']
assert push['checkpoint_commit'] == push['remote_commit'] == selection['verified_prior_checkpoint_commit']
assert push['actual_push_terminal'] and push['actual_push_terminal_exit'] == 0
assert push['actual_remote_check_terminal'] and push['actual_remote_check_terminal_exit'] == 0
assert push['postpush_current_tree_verifier_terminal_exit'] == 0
assert push['normal_Source_files'] == 6283
bound.add(ROOT / selection['prior_push_verified_receipt'])
item = selection['components'][0]
assert selection['compile_order'] == [item['module']]
assert item['kind'] == 'new_module' and item['module'] == 'SourcePruningEnumerationSharedIncomingQuerySeeds'
assert not (ROOT/'lean/MicroCFTA'/item['source']).exists(), 'The new normal Source basename must be absent.'
packet = BASE/item['packet']
manifest = json.loads(verify(packet/'MANIFEST.json',item['manifest_sha256']))
for name,record in records(manifest):
    verify(packet/name,record)
for record in json.loads((packet/'SOURCE-PINS.json').read_text())['files']:
    verify(ROOT/record['file'],record)
raw = verify(packet/item['source'],{'sha256':item['raw_sha256'],'bytes':item['raw_bytes']})
assembly = json.loads((packet/'ASSEMBLY.json').read_text())
assembled = b''.join((packet/part).read_bytes()if (packet/part).is_file()else part.encode()for part in assembly['assembly'])
assert assembled == raw and assembly['raw_sha256'] == item['raw_sha256']
assert assembly['new_public_reports'] == assembly['new_private_helpers_transitive'] - 1 == 1
assert assembly['selected_explicit_private_reports'] == assembly['new_definitions'] == assembly['definition_checks'] == 0
for header in item['headers']:
    data = verify(packet/header['file'],header['sha256'])
    assert data == (CONTROL/header['file']).read_bytes()
    start = raw.index(data.splitlines()[0])
    assert raw[start:raw.index(b':= by',start)].rstrip() == data.rstrip()
probe = verify(packet/item['probe'],item['probe_sha256'])
assert re.findall(r'^#print axioms (\S+)',probe.decode(),re.M) == item['public_qnames']
assert probe.count(b'#print axioms ') == 1 and b'#check ' not in probe
assert b'#print axioms ' not in raw and b'#check ' not in raw
assert re.findall(r'^theorem (\w+)',raw.decode(),re.M) == ['original_source_observe_preserves_seeds']
assert re.findall(r'^private theorem (\w+)',raw.decode(),re.M) == ['actual_trace_source_growth','actual_query_source_seeds']
assert not re.findall(r'^(?:private )?(?:def|inductive|structure) ',raw.decode(),re.M)
assert not re.search(rb'set_option\s+(?:maxHeartbeats|maxRecDepth|warningAsError|linter\.)',raw)
assert not re.search(rb'\b(?:sorry|axiom)\b',raw)
# The original was rejected in precompiler review. No compiler failure or proof
# credit is invented for that scope correction.
original = BASE/selection['original_packet']
original_manifest = json.loads(verify(original/'MANIFEST.json',selection['original_manifest_sha256']))
for name,record in records(original_manifest):
    verify(original/name,record)
original_raw = verify(original/item['source'],selection['original_raw_sha256'])
repair = json.loads((CONTROL/'SCOPE-REPAIR.json').read_text())
assert repair == json.loads((packet/'REPAIR.json').read_text())
old_line = repair['old_preamble_line'].encode()
new_lines = repair['new_preamble_lines'].encode()
assert original_raw.count(old_line) == 1 and raw == original_raw.replace(old_line,new_lines,1)
for filename in repair['FIRST_proof_and_probe_files_byte_exact']:
    assert (original/filename).read_bytes() == (packet/filename).read_bytes(),filename
assert not repair['proof_limits_changed'] and not repair['premises_or_conclusion_changed']
assert selection['original_rejected_before_compiler'] and selection['original_scope_rejection_has_no_compiler_run']
# Recompute all imports from the exact candidate and unchanged normal sources.
normal_objects = ROOT/'lean/.lake/build/lib/lean/MicroCFTA'
assert normal_objects.is_dir() and not (normal_objects/(item['module']+'.olean')).exists()
paths = {path.stem:path for path in sources}
active = []
seen = set()
order = []
graph = {}


def visit(name):
    assert name not in active, 'Import cycle: '+repr(active+[name])
    if name in seen:
        return
    active.append(name)
    data = raw.decode()if name == item['module']else paths[name].read_text()
    graph[name] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$',data,re.M)
    for dependency in graph[name]:
        assert dependency in paths,dependency
        visit(dependency)
    active.pop()
    seen.add(name)
    order.append(name)


visit(item['module'])
topological = json.loads((CONTROL/'TOPOLOGICAL-ORDER.json').read_text())
assert graph == topological['direct_imports'] and order == topological['full_transitive_order']
assert len(order) == 2331 and len(seen-{item['module']}) == 2330
assert 'SourcePruningEnumerationSharedTerminalQueryEvents' not in seen
for name in seen-{item['module']}:
    assert (normal_objects/(name+'.olean')).is_file(),name
assert not selection['terminal_or_later_dispatch_candidates_selected']
for name in ['shadow-compile.py.txt','check-driver.py.txt']:
    ast.parse((CONTROL/name).read_text())
# Root materializes a fresh runtime only after all read-only preflights pass.
runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-incoming-query-seeds-'))
(objects/'MicroCFTA').mkdir()
linked = []
for obj in sorted(normal_objects.glob('*.olean')):
    if obj.stem != item['module']:
        (objects/'MicroCFTA'/obj.name).symlink_to(obj)
        linked.append(obj.name)
assert item['module']+'.olean' not in linked
(runtime/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
(runtime/'shadow-imports.json').write_text(json.dumps({'linked_unchanged_modules':linked,
    'excluded_candidate_modules':[item['module']],'candidate_output_links_created':False,
    'normal_dependency_modules':2330,'cache_data_copied':False},indent=2)+'\n')
fixture = runtime/'source/MicroCFTA'/item['source']
fixture.parent.mkdir(parents=True)
fixture.write_bytes(raw+b'\n'+probe)
bound.add(fixture)
(runtime/'selection.json').write_text(json.dumps(selection,indent=2,sort_keys=True)+'\n')
(runtime/'shadow-compile.py').write_bytes((CONTROL/'shadow-compile.py.txt').read_bytes())
(runtime/'check.py').write_bytes((CONTROL/'check-driver.py.txt').read_bytes())
(runtime/'NORMAL-STAGING-GATE.json').write_text(json.dumps({'source_commit':selection['source_commit'],
    'required_Work59_push_receipt':selection['prior_push_verified_receipt'],
    'verified_checkpoint_commit':push['checkpoint_commit'],
    'normal_Source_staging_executed_by_this_controller':False,
    'terminal_or_dispatch_candidates_selected':False},indent=2)+'\n')
bound.add(Path(__file__))
bound.update(path for path in runtime.iterdir()if path.is_file())
(runtime/'source-pins.json').write_text(json.dumps({str(path.relative_to(ROOT)):SHA(path.read_bytes())
    for path in sorted(bound)},indent=2,sort_keys=True)+'\n')
print(json.dumps({'runtime':str(runtime),'objects':str(objects),'checks':1,'expected_public_reports':1,
    'explicit_private_reports':0,'new_private_helpers':2,'definition_checks':0,
    'public_and_two_private_FIRSTs_exact':True,'original_scope_rejection_before_compiler':True,
    'prior_Work59_checkpoint_push_verified':True,'normal_Source_changed':False}))
