from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-fold-and-terminal-query-seeds-staging-control-draft'
WORK = BASE/'20261118-fold-query-seeds-work'
assert Path(__file__).resolve().parent == WORK.resolve()
assert Path(__file__).read_bytes() == (CONTROL/'stage-normal-sources.py').read_bytes()
assert not (WORK/'SOURCES-NORMAL-STAGING.json').exists()
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
bound = set()


def verify(path, record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256']if isinstance(record,dict)else record),str(path)
    if isinstance(record,dict)and 'bytes'in record:
        assert len(data) == record['bytes'],str(path)
    bound.add(path)
    return data


def records(value):
    if isinstance(value,list):
        return [(entry.get('file',entry.get('path')),entry)for entry in value]
    if 'files'in value:
        return records(value['files'])
    if 'pins'in value:
        return records(value['pins'])
    return value.items()


def packet_files(packet, digest):
    manifest = json.loads(verify(packet/'MANIFEST.json',digest))
    for name,record in records(manifest['files']):
        verify(packet/name,record)


for name,record in records(read(CONTROL/'MANIFEST.json')['files']):
    verify(CONTROL/name,record)
bound.add(CONTROL/'MANIFEST.json')
for name,record in records(read(CONTROL/'RECEIPT-PINS.json')):
    verify(ROOT/name,record)
stage = read(CONTROL/'EXPECTED-STAGE.json')
assert stage['source_baseline'] == '530a41528e91526e978a954539a81b12fb8d7a60'
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6284,5284,741,336)
assert (stage['fresh_reports'],stage['inherited_reports'],stage['combined_reports']) == (3,532,535)
assert stage['new_public_theorems'] == 3 and stage['new_private_helpers_transitive'] == 0
assert stage['new_definitions'] == stage['new_Prop_definitions'] == stage['definition_checks'] == stage['explicit_private_reports'] == 0
assert stage['resource_reports_inherited'] == 264 and stage['extra_fresh_fold_recheck_credit'] == 0
prior = BASE/'20261118-terminal-query-resources-work'
publication = BASE/'20261118-terminal-and-query-seeds-publication'
commit = read(prior/'SOURCE-COMMIT.json')
commit_actual = read(prior/'SOURCE-COMMIT-ACTUAL-RUN.json')
pub_verified = read(prior/'PUBLICATION-VERIFIED.json')
pub_actual = read(prior/'PUBLICATION-ACTUAL-RUN.json')
published = read(publication/'checked.json')
assert commit['source_commit'] == commit_actual['source_commit'] == stage['source_baseline']
assert commit['actual_terminal']and commit_actual['actual_terminal']
assert commit['actual_terminal_exit'] == commit_actual['actual_terminal_exit'] == 0
assert commit_actual['actual_session'] == 68342
assert pub_verified['actual_session'] == pub_actual['actual_session'] == commit['publication_actual_session'] == 88140
assert pub_verified['actual_terminal']and pub_actual['actual_terminal']
assert pub_verified['actual_terminal_exit'] == pub_actual['actual_terminal_exit'] == 0
assert published == read(publication/'results.json') and pub_verified['checks'] == published['checks']
assert [entry['total_axiom_reports']for entry in published['checks']] == [738,3,333,738,738]
assert all(entry['exit'] == 0 and not entry['diagnostics']and not entry['sorryAx']and not entry['nonstandard_axioms']
    and entry['declaration_checks'] == 0 for entry in published['checks'])
assert published['all_five_gates_passed']and published['source_pins_unchanged']
assert SHA((publication/'checked.json').read_bytes()) == pub_verified['checked_sha256']
pub_pins = json.loads(verify(publication/'source-pins.json',pub_verified['source_pins_sha256']))
assert len(pub_pins) == pub_verified['pins_independently_reverified'] == 8803
for name,record in pub_pins.items():
    verify(ROOT/name,record)
push = read(ROOT/stage['prior_checkpoint_push_receipt'])
assert push['source_commit'] == stage['source_baseline']
assert push['checkpoint_commit'] == push['remote_commit'] == stage['prior_checkpoint'] == '862d4879e201a8ace8b42b42398be7a5cfa37533'
assert push['actual_push_terminal']and push['actual_remote_check_terminal']
assert push['actual_push_terminal_exit'] == push['actual_remote_check_terminal_exit'] == push['postpush_current_tree_verifier_terminal_exit'] == 0
assert push['normal_Source_files'] == 6284
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT).decode().strip() == 'formalize'
subprocess.run(['git','merge-base','--is-ancestor',stage['source_baseline'],'HEAD'],cwd=ROOT,check=True)
changes = subprocess.check_output(['git','diff','--name-only',stage['source_baseline'],'HEAD'],cwd=ROOT).decode().splitlines()
assert all(name in ['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md']or name.startswith('lean/restart-evidence/')for name in changes)
subprocess.run(['git','diff','--quiet',stage['source_baseline'],'HEAD','--','lean/MicroCFTA',
    'shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json'],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT)
baseline = json.loads(verify(ROOT/stage['source_baseline_path'],stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6284 and len(baseline['toolchain']) == 4
assert {str(path.relative_to(ROOT))for path in (ROOT/'lean/MicroCFTA').glob('*.lean')} == set(baseline['sources'])
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    verify(ROOT/name,record)
    assert pub_pins[name] == record['sha256']
# The combined check selects three distinct laws. The earlier fold check is a prerequisite.
checks = read(CONTROL/'PRIVATE-CHECKS.json')
assert len(checks) == 2 and [entry['fresh_public_reports']for entry in checks] == [3,0]
for entry in checks:
    verified = read(ROOT/entry['verified_receipt'])
    actual = read(ROOT/entry['actual_receipt'])
    runtime = BASE/entry['runtime']
    checked = json.loads(verify(runtime/'checked.json',verified['checked_sha256']))
    assert checked == json.loads(verify(runtime/'results.json',verified['results_sha256']))
    assert verified['actual_session'] == actual['actual_session'] == entry['actual_session']
    assert verified['actual_terminal']and actual['actual_terminal']
    assert verified['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
    assert verified['checks'] == checked['checks']and verified['proof_credit']and verified['source_pins_unchanged']
    assert sum(item['total_axiom_reports']for item in checked['checks']) == entry['expected_reports']
    assert all(item['exit'] == 0 and not item['diagnostics']and not item['sorryAx']and not item['nonstandard_axioms']
        and item['declaration_checks'] == item['axiom_free_reports'] == 0 for item in checked['checks'])
    assert checked['limits'] == {'memory.max':'8589934592','memory.high':'8589934592','memory.swap.max':'0'}
    pins = json.loads(verify(runtime/'source-pins.json',verified['source_pins_sha256']))
    assert len(pins) == verified['pins_independently_reverified'] == entry['pins']
    for name,record in pins.items():
        verify(ROOT/name,record)
    packet_files(BASE/entry['control'],entry['control_manifest_sha256'])
    if entry['name'] == 'combined':
        assert verified['executed_control'] == actual['executed_control'] == entry['control']
        assert verified['executed_control_manifest_sha256'] == actual['executed_control_manifest_sha256'] == entry['control_manifest_sha256']
        assert verified['previously_checked_fold_reports_rebuilt'] == 2 and verified['additive_credit_for_rebuilt_fold_reports'] == 0
rejected = read(ROOT/stage['rejected_preparer_receipt'])
assert rejected['actual_terminal'] and rejected['actual_terminal_exit'] == 1
assert not rejected['compiler_started'] and not rejected['runtime_or_tmp_created'] and rejected['proof_credit'] == 0
assert rejected['actual_tool_chunk'] == 'a1bbf9'
packet_files(BASE/rejected['original_control'],rejected['original_control_manifest_sha256'])
components = read(CONTROL/'COMPONENTS.json')['components']
assert components == stage['components']and len(components) == 2
fold,term = components
combined = read(BASE/checks[0]['control']/'SELECTION.json')
assert [item['module']for item in components] == combined['compile_order'] == stage['compile_order']
raws = {}
for component,selected in zip(components,combined['components']):
    for key in ['module','packet','manifest_sha256','source','raw_sha256','raw_bytes','probe','probe_sha256','public_qnames','expected_axiom_reports','expected_declaration_checks']:
        assert component[key] == selected[key],(component['module'],key)
    packet = BASE/component['packet']
    packet_files(packet,component['manifest_sha256'])
    for filename in ['SOURCE-PINS.json','ADDITIONAL-SOURCE-PINS.json','DEPENDENCY-PINS.json']:
        if (packet/filename).exists():
            for name,record in records(read(packet/filename)):
                verify(ROOT/name,record)
    raw = verify(packet/component['source'],{'sha256':component['raw_sha256'],'bytes':component['raw_bytes']})
    for header in component['all_headers']:
        full = verify(ROOT/header['file'],header['sha256']).rstrip()
        assert raw.count(full) == 1 and re.match(rb'\s*:= by',raw[raw.index(full)+len(full):])
    probes = verify(packet/component['probe'],component['probe_sha256'])
    assert re.findall(r'^#print axioms (\S+)',probes.decode(),re.M) == component['public_qnames']
    assert b'#check 'not in probes and b'#print axioms 'not in raw and b'#check 'not in raw
    fixture = BASE/checks[0]['runtime']/'source/MicroCFTA'/component['source']
    assert verify(fixture,SHA(fixture.read_bytes())) == raw+b'\n'+probes
    raws[component['module']] = raw
before_fold = verify(ROOT/fold['source_path'],{'sha256':fold['owner_sha256'],'bytes':36968})
before_term = verify(ROOT/term['source_path'],{'sha256':term['owner_sha256'],'bytes':39276})
assert before_fold == (CONTROL/'FOLD-BEFORE.lean.txt').read_bytes()
assert before_term == (CONTROL/'TERMINAL-BEFORE.lean.txt').read_bytes()
fold_packet,term_packet = BASE/fold['packet'],BASE/term['packet']
raw_packet = BASE/fold['raw_base_packet']
packet_files(raw_packet,fold['raw_base_manifest_sha256'])
raw_base = verify(raw_packet/fold['source'],fold['raw_base_sha256'])
assert len(raw_base) == 47686 and raw_base == (raw_packet/'IMPORTS.lean.txt').read_bytes()+before_fold+(raw_packet/'APPEND.lean.txt').read_bytes()
assert raws[fold['module']] == raw_base+(fold_packet/'APPEND.lean.txt').read_bytes()
assert raws[term['module']] == (term_packet/'IMPORTS.lean.txt').read_bytes()+before_term+(term_packet/'APPEND.lean.txt').read_bytes()
for item,old in [(fold,before_fold),(term,before_term)]:
    assert raws[item['module']][66:66+len(old)] == old
for packet in [raw_packet,fold_packet,term_packet]:
    appended = (packet/'APPEND.lean.txt').read_bytes()
    assert len(re.findall(rb'^theorem ',appended,re.M)) == 1
    assert not re.search(rb'^private theorem |^(?:private )?(?:def|structure|inductive) ',appended,re.M)
    assert not re.search(rb'set_option\s+(maxHeartbeats|maxRecDepth|warningAsError|linter\.)',appended)
normal = {path.stem:path for path in (ROOT/'lean/MicroCFTA').glob('*.lean')}
active,seen,order,graph = [],set(),[],{}


def visit(name):
    assert name not in active,name
    if name in seen:
        return
    active.append(name)
    text = raws[name].decode()if name in raws else normal[name].read_text()
    graph[name] = re.findall(r'^import MicroCFTA\.([A-Za-z0-9_]+)\s*$',text,re.M)
    for dependency in graph[name]:
        visit(dependency)
    active.pop()
    seen.add(name)
    order.append(name)


for name in stage['compile_order']:
    visit(name)
topology = read(CONTROL/'TOPOLOGICAL-ORDER.json')
assert graph == topology['direct_imports']and order == topology['full_transitive_order']
assert [name for name in order if name in raws] == stage['compile_order']
audit_path = ROOT/'lean/MicroCFTA/Audit.lean'
old_audit = verify(audit_path,{'sha256':stage['old_audit_sha256'],'bytes':435886})
assert old_audit == (CONTROL/'AUDIT-BEFORE.lean.txt').read_bytes()
imports = (CONTROL/'IMPORTS.lean.txt').read_bytes()
probes = verify(CONTROL/'PUBLIC-PROBES.lean.txt',stage['public_probes_sha256'])
assert imports == b''and probes == b''.join((BASE/item['packet']/item['probe']).read_bytes()for item in components)
assert len(re.findall(rb'^#print axioms ',probes,re.M)) == 3
new_audit = old_audit+b'\n'+probes
assert SHA(new_audit) == stage['staged_audit_sha256']and len(new_audit) == stage['staged_audit_bytes']
assert new_audit[:435886] == old_audit
assert len(re.findall(rb'^import ',new_audit,re.M)) == 5284
assert len(re.findall(rb'^#print axioms ',old_audit,re.M)) == 738 and len(re.findall(rb'^#print axioms ',new_audit,re.M)) == 741
for item in components:
    for qname in item['public_qnames']:
        assert ('#print axioms '+qname).encode()not in old_audit
expected = json.loads(verify(CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json',stage['expected_normal_source_pins_sha256']))
assert len(expected) == 6288
assert set(stage['exact_Source_write_paths']) == {fold['source_path'],term['source_path'],'lean/MicroCFTA/Audit.lean'}
assert set(stage['baseline_overrides']) == set(stage['exact_Source_write_paths'])
assert stage['old_other_Source_files_byte_exact'] == 6281 and stage['new_modules'] == 0
snapshots = {ROOT/fold['old_snapshot']:before_fold,ROOT/term['old_snapshot']:before_term,
    ROOT/stage['baseline_overrides']['lean/MicroCFTA/Audit.lean']:old_audit}
assert all(not path.exists()for path in snapshots)
assert all(not(WORK/name).exists()for name in ['IMPORTS.lean.txt','PUBLIC-PROBES.lean.txt','NORMAL-SOURCE-PINS.json'])
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    module = Path(name).stem
    expected_digest = SHA(raws[module])if module in raws else SHA(new_audit)if name == 'lean/MicroCFTA/Audit.lean'else record['sha256']
    assert expected[name] == expected_digest
bound.add(Path(__file__))
preflight_pins = {str(path.relative_to(ROOT)):SHA(path.read_bytes())for path in bound}
for name,digest in preflight_pins.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
# Only Root executes the following three normal Source writes after all gates pass.
for path,data in snapshots.items():
    path.write_bytes(data)
for item in components:
    (ROOT/item['source_path']).write_bytes(raws[item['module']])
audit_path.write_bytes(new_audit)
assert len(list((ROOT/'lean/MicroCFTA').glob('*.lean'))) == 6284
for name,digest in expected.items():
    assert SHA((ROOT/name).read_bytes()) == digest,name
for name,digest in preflight_pins.items():
    assert SHA((ROOT/stage['baseline_overrides'].get(name,name)).read_bytes()) == digest,name
for name in ['IMPORTS.lean.txt','PUBLIC-PROBES.lean.txt']:
    (WORK/name).write_bytes((CONTROL/name).read_bytes())
(WORK/'NORMAL-SOURCE-PINS.json').write_bytes((CONTROL/'EXPECTED-NORMAL-SOURCE-PINS.json').read_bytes())
actual_stage = dict(stage)
actual_stage.update(status='SOURCE_NORMAL_STAGING_COMPLETED',staged_at=datetime.datetime.now().astimezone().isoformat(),
    actual_private_sessions=[entry['actual_session']for entry in reversed(checks)],selected_private_sessions=[checks[0]['actual_session']],
    fold_prerequisite_session=3921,normal_Source_changed=True,published=False,
    actual_Source_files=6284,actual_audit_imports=5284,actual_audit_reports=741,
    prior_source_checkpoint_push_verified=True,normal_source_pins_sha256=SHA((WORK/'NORMAL-SOURCE-PINS.json').read_bytes()))
(WORK/'SOURCES-NORMAL-STAGING.json').write_text(json.dumps(actual_stage,indent=2)+'\n')
print(json.dumps(actual_stage,indent=2))
