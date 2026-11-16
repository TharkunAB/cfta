from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
evidence = root / 'lean/restart-evidence'
packet = '20261116-real-callback-and-isolation-checkpoint'
prior_packet = '20261116-real-prefix-all-outcome-checkpoint'
prior_work = evidence / '20261116-real-prefix-all-outcome-checkpoint-work'
base = 'ca5a4bcbd0ea06e92d332f50c16190aaa97be4d1'
code = 'd84774febecbb4e0d5cd3d256c2394f2be1dc441'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip() == code
public = evidence / '20261116-real-callback-and-isolation-publication'
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] for x in result['checks'])
config = dict(result,checked_code=code,prior_checkpoint=base,public_run=str(public),
    public_gates=5,explicit_reports=418,source_files=6126,direct_audit_imports=5126,
    board_prefix='current-board-public-',new_modules=4,new_public_theorems=5,
    old_non_audit_sources_byte_exact=6121,old_audit_bytes_preserved_as_exact_block=True,
    native_CM_query_scope='One literal initial node query; both complete memo families initially empty.',
    full_scope='One finite accepted completion of each same original emitted partial root under one compatible assignment, including domains, paths, UF aliases, residuals, readback, parked recompletion and every removed historical obligation on that branch; preserve original source/root/noStop, inputs, fuels, budgets and all emissions before later stops.')
(work / 'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
prefixes = ('20261116-current-real-worker-callback-',
    '20261116-current-real-captured-callback-',
    '20261116-current-real-prefix-earlier-isolated-',
    '20261116-current-real-prefix-native-readback-',
    '20261116-current-real-nullary-captured-frame-',
    '20261116-current-any-budget-identity-small-unfold-instance-',
    '20261116-current-any-budget-identity-verified-components-',
    '20261116-current-warm-',
    '20261116-current-source-recursive-boundary-',
    '20261116-current-source-startup-recursive-inhabitance-')
roots = []
for p in sorted(evidence.iterdir()):
    if p.is_dir() and p.name.startswith(prefixes) and any((p / name).exists() for name in ['MANIFEST.sha256','MANIFEST.json']):
        roots.append(p)
roots += [work,public,prior_work]
for name in ['20261116-native-identity-components-and-types-check',
    '20261116-native-small-identity-and-real-callback-check',
    '20261116-native-repaired-callback-isolation-and-small-check',
    '20261116-native-callback-and-isolation-repairs-check',
    '20261116-native-real-captured-callback-check',
    '20261116-native-earlier-isolation-normalization-check',
    '20261116-native-prefix-native-readback-check',
    '20261116-native-prefix-native-readback-bool-check',
    '20261116-native-identity-verified-components-check']:
    p = evidence / name
    assert (p / 'checks.json').exists()
    roots.append(p)
roots = list(dict.fromkeys(roots))
(work / 'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots],indent=2)+'\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({'prior_immutable_checkpoints_retained':True,
    'live_or_unfinished_agent_packets_excluded':True,'no_live_compiler_outputs_selected':True},indent=2)+'\n')
(work / 'selection-review.json').write_text(json.dumps({'selected_roots':len(roots),
    'all_promoted_raw_candidates_and_failed_parents_retained':True,
    'identity609_and_nullary271_retained_as_uncompiled':True,
    'type_only_pass_is_not_proof_credit':True,
    'lost_first34657failure_log_not_claimed_retained':True,
    'unique_job_names_fix_and_recovered37245logs_retained':True,
    'compiled_objects_excluded':True,'original_full_scope_preserved':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text = (prior_work / name).read_text().replace(prior_packet,packet)
    text = text.replace("BASE = '79155bfa2a24ad0629e97f67e08419b46a0dc248'", "BASE = '"+base+"'")
    text = text.replace('# Every real-prefix outcome and continuing-branch resource checkpoint',
        '# Actual callbacks and earlier parked-marker preservation checkpoint')
    (work / name).write_text(text)
text = (evidence / prior_packet / 'verify.py').read_text().replace(prior_packet,packet)
(work / 'verify.py').write_text(text)
print(json.dumps({'checked_code':code,'selected_roots':len(roots),'public_gates':5}))
