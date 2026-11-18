from pathlib import Path
import ast
import gzip
import hashlib
import json
import re
import subprocess
ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT/'lean/restart-evidence'
CONTROL = BASE/'20261118-no-mu-native-inventory-checkpoint-control-draft'
WORK = BASE/'20261118-no-mu-native-inventory-work'
RUNTIME = BASE/'20261118-no-mu-native-inventory-publication'
ARCHIVE = BASE/'20261118-no-mu-native-inventory-checkpoint'
PRIOR = BASE/'20261118-source-inventory-local-coverage-checkpoint'
PUBLICATION_CONTROL = BASE/'20261118-no-mu-native-inventory-publication-control-draft'
BOARD = 'current-board-no-mu-native-inventory-'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
git = lambda *args: subprocess.check_output(['git',*args],cwd=ROOT)
assert (CONTROL/'STATUS.txt').read_text().startswith('FROZEN'),'OPEN control; do not execute.'
assert Path(__file__).resolve().parent == WORK and Path(__file__).read_bytes() == (CONTROL/'prepare-checkpoint-controls.py').read_bytes()

def verify(path,record):
    data = path.read_bytes()
    assert SHA(data) == (record['sha256'] if isinstance(record,dict) else record),str(path)
    if isinstance(record,dict) and 'bytes' in record:
        assert len(data) == record['bytes']
    return data

def packet(path,digest=None):
    if digest:
        verify(path/'MANIFEST.json',digest)
    for name,record in read(path/'MANIFEST.json')['files'].items():
        verify(path/name,record)

packet(CONTROL)
for name,digest in read(CONTROL/'SOURCE-PINS.json').items():
    verify(ROOT/name,digest)
stage = read(WORK/'SOURCES-NORMAL-STAGING.json')
assert stage['status'] == 'SOURCE_NORMAL_STAGING_COMPLETED'
assert (stage['source_files'],stage['audit_imports'],stage['audit_reports'],stage['independent_reports']) == (6291,5291,752,347)
assert (stage['fresh_public_reports'],stage['fresh_private_reports'],stage['inherited_reports'],stage['combined_reports']) == (1,0,568,569)
assert stage['new_public_theorems'] == 1 and stage['new_private_theorems'] == stage['new_definitions'] == stage['new_private_helpers_transitive'] == 0
assert set(stage['baseline_overrides']) == {'lean/MicroCFTA/Audit.lean'}
overrides = stage['baseline_overrides']
def historical(name,record):
    digest = record['sha256'] if isinstance(record,dict) else record
    for path in [ROOT/name,ROOT/overrides.get(name,name)]:
        if path.is_file() and SHA(path.read_bytes()) == digest:
            return verify(path,record)
    raise AssertionError(name)

source,provenance = read(WORK/'SOURCE-COMMIT.json'),read(WORK/'SOURCE-COMMIT-ACTUAL-RUN.json')
commit = source['source_commit']
assert commit == provenance['source_commit'] and re.fullmatch('[0-9a-f]{40}',commit)
assert provenance['actual_terminal'] and provenance['actual_terminal_exit'] == 0
assert source['parent'] == stage['prior_checkpoint'] == 'ef5cd82556c4edc671fcbecd8197ae222b11f3b1'
commit_control = BASE/provenance['controller']
assert commit_control.name == '20261118-no-mu-native-inventory-source-commit-control-draft'
packet(commit_control,provenance['control_manifest_sha256'])
assert (WORK/'commit-source.py').read_bytes() == verify(commit_control/'commit-source.py',provenance['script_sha256'])
assert read(commit_control/'MANIFEST.json')['all_final_receipts_bound_before_freeze']
assert git('branch','--show-current').decode().strip() == 'formalize' and git('rev-parse','HEAD').decode().strip() == commit
assert git('rev-parse',commit+'^').decode().strip() == source['parent'] and not git('status','--porcelain','--untracked-files=no')
assert set(git('diff','--name-only',source['parent'],commit).decode().splitlines()) == set(stage['exact_Source_write_paths'])
for name in stage['exact_Source_write_paths']:
    assert git('show',commit+':'+name) == (ROOT/name).read_bytes()
    if name in overrides:
        assert git('show',source['parent']+':'+name) == (ROOT/overrides[name]).read_bytes()
    else:
        assert not git('ls-tree','--name-only',source['parent'],'--',name)
for name in ['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md']:
    assert (ROOT/name).read_bytes() == git('show',commit+':'+name)
publication,actual = read(WORK/'PUBLICATION-VERIFIED.json'),read(WORK/'PUBLICATION-ACTUAL-RUN.json')
assert publication['actual_session'] == actual['actual_session'] == source['publication_actual_session']
assert publication['actual_terminal'] and actual['actual_terminal'] and publication['actual_terminal_exit'] == actual['actual_terminal_exit'] == 0
report = json.loads(verify(RUNTIME/'checked.json',publication['checked_sha256']))
assert report == json.loads(verify(RUNTIME/'results.json',publication['results_sha256'])) and report['checks'] == publication['checks']
assert [e['total_axiom_reports'] for e in report['checks']] == [752,1,347,752,752]
assert [e['declaration_checks'] for e in report['checks']] == [0,0,0,0,0]
assert all(e['exit'] == 0 and not e['diagnostics'] and not e['sorryAx'] and not e['nonstandard_axioms'] for e in report['checks'])
assert report['all_five_gates_passed'] and report['source_pins_unchanged']
assert report['audited_theorems'] == publication['audited_theorems'] == source['audited_theorems']
public_pins = json.loads(verify(RUNTIME/'source-pins.json',publication['source_pins_sha256']))
assert len(public_pins) == publication['pins_independently_reverified']
for name,record in public_pins.items():
    verify(ROOT/name,record)
private_meta = read(PUBLICATION_CONTROL/'PRIVATE-CHECK.json')
private,private_actual = read(ROOT/private_meta['verified_receipt']),read(ROOT/private_meta['actual_receipt'])
assert private['actual_session'] == private_actual['actual_session'] == stage['actual_private_session']
assert private['actual_terminal'] and private_actual['actual_terminal'] and private['actual_terminal_exit'] == private_actual['actual_terminal_exit'] == 0
private_run = BASE/private['runtime']
private_report = json.loads(verify(private_run/'checked.json',private['checked_sha256']))
assert private_report == json.loads(verify(private_run/'results.json',private['results_sha256'])) and private_report['checks'] == private['checks']
assert [e['total_axiom_reports'] for e in private_report['checks']] == [1]
for name,record in json.loads(verify(private_run/'source-pins.json',private['source_pins_sha256'])).items():
    historical(name,record)
assert stage['fresh_classification']['per_qname'] == source['per_qname_classification']
baseline = json.loads(verify(ROOT/stage['source_baseline_path'],stage['source_baseline_sha256']))
assert len(baseline['sources']) == 6290 and len(baseline['toolchain']) == 4
for name,record in {**baseline['sources'],**baseline['toolchain']}.items():
    historical(name,record)
assert len(set(baseline['sources'])-set(overrides)) == 6289
component = stage['components'][0]
selected = BASE/component['packet'];packet(selected,component['manifest_sha256'])
raw = verify(ROOT/component['source_path'],{'bytes':component['raw_bytes'],'sha256':component['raw_sha256']})
assert raw == (selected/component['source']).read_bytes()
for name,digest in component['headers'].items():
    header = verify(selected/name,digest)
    assert sum(raw.count(h+b' := by\n') for h in [header]+([header[:-1]] if header.endswith(b'\n') else [])) == 1
assert raw.count(verify(selected/component['proof'],component['proof_sha256'])) == 1
old_audit = historical('lean/MicroCFTA/Audit.lean',baseline['sources']['lean/MicroCFTA/Audit.lean'])
assert len(old_audit) == 437705 and (ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()[50:50+437705] == old_audit
bindings = read(CONTROL/'prior-bindings.json')
for name,key in [('manifest.json','prior_manifest_sha256'),('checkpoint.json','prior_checkpoint_json_sha256')]:
    data = verify(PRIOR/name,bindings[key])
    assert git('show',source['parent']+':'+str((PRIOR/name).relative_to(ROOT))) == data
for name,record in json.loads(gzip.decompress((PRIOR/'source-pins.json.gz').read_bytes())).items():
    historical(name,record)
request,canonical = read(WORK/(BOARD+'request.json')),read(WORK/(BOARD+'canonical.json'))
assert canonical['verified'];post = canonical.get('post',canonical)
assert post['id'] == request['request_id'] and type(post['sequence']) is int
for key,value in [('author',request['username']),('thread_id',request['thread_id']),('post_type',request['post_type']),('content',request['content']),('metadata',request['metadata'])]:
    assert post[key] == value
assert post['metadata']['source'] == commit and not post['metadata']['joint_finite_completion_proved']
cleanup = read(WORK/'COMBINED-TMP-CLEANUP.json')
assert {e['actual_session']:e['runtime'] for e in cleanup['runs']} == {private['actual_session']:private_run.name,actual['actual_session']:RUNTIME.name}
assert cleanup['all_targets_removed'] and cleanup['normal_cache_preserved'] and cleanup['unknown_tmp_entries_preserved'] and cleanup['no_cache_data_copied']
cumulative = 7984937229
for e in cleanup['runs']:
    assert e['prior_cumulative_removed_bytes'] == cumulative
    cumulative += e['regular_bytes_removed'];assert e['cumulative_removed_bytes'] == cumulative
    assert e['owned_terminal_only'] and e['all_targets_removed'] and e['normal_cache_preserved'] and e['no_cache_data_copied'] and not e['live_process_references']
    assert e['scope_ActiveState'] == 'inactive' and e['generated_terminal_outputs_only'] and e['no_source_or_normal_cache_data_unlinked']
    assert not Path(e['path']).exists() and not Path(e['path']).is_symlink()
assert cumulative == cleanup['cumulative_removed_bytes']
assert sum(e['regular_bytes_removed'] for e in cleanup['runs']) == cleanup['regular_bytes_removed_this_batch']
assert sum(e['symlinks_removed'] for e in cleanup['runs']) == cleanup['symlinks_removed_this_batch']
start = read(WORK/'START.json')
assert start['expected_new_public_reports'] == 1 and start['expected_new_private_reports'] == start['new_definitions_helpers_constructors'] == 0
assert not start['goal_status_change_performed'] and not start['goal_completion_claimed']
resume = read(BASE/'20261118-source-entry-endpoint-seeds-work/RESUME-AUTHORIZATION.json')
assert resume['manual_work_explicitly_authorized'] and resume['earlier_usage_pause_lifted'] and not resume['goal_status_change_performed']
historical_usage = read(ROOT/read(CONTROL/'historical-usage-selection.json')['path'])
current_path = ROOT/read(CONTROL/'current-usage-selection.json')['path'];current = read(current_path)
assert not current['pause_required'] and current['pause_threshold_percent'] == 80
assert commit in (WORK/'LIVE-HANDOFF.md').read_text()
roots = read(CONTROL/'selection-roots.json')
assert len(roots) == len(set(roots)) and PRIOR.name not in roots and read(CONTROL/'archive-additional-roots.json') == []
assert all((BASE/n).is_dir() and not (BASE/n).is_symlink() for n in roots)
selected_roots = sorted(str((BASE/n).relative_to(ROOT)) for n in roots)
source_pins = {n:v for n,v in public_pins.items() if n.startswith('lean/MicroCFTA/') and n.endswith('.lean')}
assert len(source_pins) == 6291
tree = hashlib.sha256()
for name,digest in sorted(source_pins.items()):
    tree.update(name.encode()+b'\0'+digest.encode()+b'\n')
config = dict(report)
config.update(checked_code=commit,prior_checkpoint=source['parent'],public_run=str(RUNTIME),public_gates=5,explicit_reports=752,board_prefix=BOARD,board_post_id=post['id'],board_sequence=post['sequence'],source_tree_sha256=tree.hexdigest(),old_other_Source_files_byte_exact=6289,known_cumulative_tmp_removed_bytes=cumulative,cleanup_receipt='COMBINED-TMP-CLEANUP.json',removed_regular_bytes=cleanup['regular_bytes_removed_this_batch'],removed_symlinks=cleanup['symlinks_removed_this_batch'],historical_primary_usage_percent=historical_usage['rate_limits']['primary']['used_percent'],historical_primary_usage_checked_at=historical_usage['checked_at'],current_usage_not_measured=False,current_primary_usage_percent=current['used_percent'],current_primary_usage_checked_at=current['sample_at'],current_usage_receipt=str(current_path.relative_to(ROOT)),prior_immutable_archive=PRIOR.name,prior_manifest_sha256=bindings['prior_manifest_sha256'],actual_selected_private_sessions=[private['actual_session']],actual_publication_session=actual['actual_session'],actual_source_commit_session=provenance['actual_session'],executed_source_commit_control=commit_control.name,persistent_goal_control_status='paused',work_authorized_by_explicit_user_resume=True,goal_active=False,goal_completion_claimed=False)
note = (CONTROL/'checkpoint-note.md').read_text()
for key,value in {'THEOREMS':report['audited_theorems'],'PINS':publication['pins_independently_reverified'],'OWNED_DIRS':len(cleanup['runs']),'REMOVED':cleanup['regular_bytes_removed_this_batch'],'SYMLINKS':cleanup['symlinks_removed_this_batch'],'CLEANUP':cumulative,'USAGE':current['used_percent'],'USAGE_TIME':current['sample_at'],'BOARD':post['sequence']}.items():
    note = note.replace('{{'+key+'}}',str(value))
assert set(re.findall(r'\{\{(.*?)\}\}',note)) == {'TIME','TREE','CODE'}
assert not ARCHIVE.exists()
outputs = {'checkpoint-config.json':config,'archive-roots.json':selected_roots,'skipped-published-roots.json':sorted(str(p.relative_to(ROOT)) for p in BASE.iterdir() if p.is_dir() and p.name.startswith(('20261117-','20261118-')) and str(p.relative_to(ROOT)) not in selected_roots),'selection-review.json':dict(selected_roots=len(roots),fresh_public_reports=1,fresh_private_reports=0,inherited_reports=568,combined_reports=569,new_public_theorems=1,new_private_theorems=0,new_definitions=0,joint_finite_completion_proved=False)}
assert all(not (WORK/n).exists() for n in outputs)
# Root writes derived checkpoint inputs only after all final gates pass.
for name,value in outputs.items():
    (WORK/name).write_text(json.dumps(value,indent=2)+'\n')
(WORK/'checkpoint-note.md').write_text(note)
print(json.dumps(dict(archive=ARCHIVE.name,checked_code=commit,roots=len(roots))))
