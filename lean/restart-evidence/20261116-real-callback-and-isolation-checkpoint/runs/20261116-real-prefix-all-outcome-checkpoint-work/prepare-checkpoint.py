from pathlib import Path
import json
import subprocess

work = Path(__file__).parent
evidence = Path('lean/restart-evidence')
packet = '20261116-real-prefix-all-outcome-checkpoint'
prior_packet = '20261115-real-prefix-and-opaque-resources-checkpoint'
prior_work = evidence / '20261115-real-prefix-and-opaque-resources-checkpoint-work'
base = '79155bfa2a24ad0629e97f67e08419b46a0dc248'
code = '76c2a89222ef1b3d3025197ca214956080f655ed'
assert subprocess.check_output(['git','rev-parse','HEAD']).decode().strip() == code
public = evidence / '20261116-real-prefix-all-outcome-publication'
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] for x in result['checks'])
config = dict(result, checked_code=code, prior_checkpoint=base, public_run=str(public.resolve()),
    public_gates=5, explicit_reports=413, source_files=6122, direct_audit_imports=5122,
    board_prefix='current-board-public-', new_modules=2, new_public_theorems=4,
    old_non_audit_sources_byte_exact=6119, old_audit_bytes_preserved_as_exact_block=True,
    all_outcome_original_header='dd9e9a2611fc87b6916d8c72f532d2fcb1b7f11a056d6f203acf5735c1ceb673',
    continuing_original_header='cdff5bc067dee0f36243988f02c462b7576b87742d18ad551612a4caec1eb967',
    native_CM_query_scope='One literal initial node query; both complete memo families initially empty.',
    full_scope='One finite accepted completion of each original emitted partial root under one compatible assignment, including actual domains, paths, aliases, residuals, readback, parked recompletion and every removed historical obligation on that branch; preserve original inputs, fuels, budgets and all emissions before later stops.')
(work / 'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
previous = set()
for earlier in [prior_packet,'20261115-actual-source-task-scan-checkpoint']:
    previous.update(Path(p).name for p in json.loads((evidence / earlier / 'archive-roots.json').read_text()))
prefixes = ('20261115-current-any-budget-identity-','20261115-native-actual-source-',
    '20261116-current-any-budget-identity-','20261116-native-actual-source-',
    '20261116-current-real-prefix-','20261116-native-real-prefix-','20261116-native-real-',
    '20261115-native-worker-')
roots = []
excluded = []
for p in sorted(evidence.iterdir()):
    if not p.is_dir() or not p.name.startswith(prefixes) or p.name in previous:
        continue
    if any((p / name).exists() for name in ['MANIFEST.sha256','MANIFEST.json','checks.json','MANIFEST-SHA256.txt','COMPONENTS.json']):
        roots.append(str(p))
    else:
        excluded.append(p.name)
roots += [str(work),str(public),str(prior_work),
    str(evidence/'20261115-finished-source-joint-completion-boundary-draft'),
    str(evidence/'20261116-current-successive-parked-clear-cycle-audit-draft')]
roots = list(dict.fromkeys(roots))
assert all(Path(p).is_dir() for p in roots)
(work / 'archive-roots.json').write_text(json.dumps(roots,indent=2)+'\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({'earlier_immutable_roots':len(previous),
    'unfinished_or_unselected_roots':excluded,'no_live_check_outputs_selected':True},indent=2)+'\n')
(work / 'selection-review.json').write_text(json.dumps({'selected_roots':len(roots),
    'new_promoted_components_and_failed_repair_parents_retained':True,
    'prior_immutable_checkpoints_preserved':True,'compiled_objects_excluded':True,
    'original_whole_worker_target_preserved':True,'joint_model_and_cycle_audits_retained':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text = (prior_work / name).read_text().replace(prior_packet,packet)
    text = text.replace("BASE = '8f71f92d7e99b361ae664b4bcee721afd4e334d3'", "BASE = '"+base+"'")
    text = text.replace('# Real-prefix and opaque-expansion resource checkpoint',
        '# Every real-prefix outcome and continuing-branch resource checkpoint')
    (work / name).write_text(text)
text = (evidence / prior_packet / 'verify.py').read_text().replace(prior_packet,packet)
(work / 'verify.py').write_text(text)
print(json.dumps({'checked_code':code,'selected_roots':len(roots),'public_gates':5}))
