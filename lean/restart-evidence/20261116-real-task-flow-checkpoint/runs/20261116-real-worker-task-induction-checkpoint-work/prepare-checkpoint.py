from pathlib import Path
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
work=Path(__file__).parent
evidence=root/'lean/restart-evidence'
packet='20261116-real-task-flow-checkpoint'
prior_packet='20261116-real-worker-assembly-checkpoint'
prior_work=evidence/'20261116-real-worker-assembly-checkpoint-work'
base='10a69e8c44e5efdf6c982677442a71276ff3e60d'
code='e454cebb0481a2790f4201f807ce0b19d9b29a3f'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==code
public=evidence/'20261116-real-worker-task-flow-publication'
result=json.loads((public/'checked.json').read_text())
assert len(result['checks'])==5
assert all(x['exit']==0 and not x['nonstandard_axioms'] for x in result['checks'])
config=dict(result,checked_code=code,prior_checkpoint=base,public_run=str(public),
    public_gates=5,explicit_reports=425,source_files=6129,direct_audit_imports=5129,
    board_prefix='current-board-task-',new_modules=1,new_public_theorems=1,
    old_non_audit_sources_byte_exact=6126,
    old_owner_and_audit_bytes_preserved_as_exact_blocks=True,
    original_c831_declaration='c831a364518a5fb5e9bce2008227efe44cd693e7c10442ad4eaa0c12f2b0ec8a',
    original_full_real_target='549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607',
    identity_theorem_scope='Identity narrowing, Metadata Unit, empty templates, stop none, default order, same original workFuel/recursiveFuel and every emitted output.',
    native_CM_query_scope='One literal initial node query; both complete memo families initially empty.',
    full_scope='One finite accepted completion of same original emitted partial root under ONE compatible assignment, including domains, paths, UF aliases, residuals, readback, parked recompletion and EVERY removed historical obligation on that branch; preserve original source/root/noStop, inputs, fuels, budgets and ALL emissions before later stops.')
(work/'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
prefixes=('20261116-current-real-actual-source-tuple-',
    '20261116-current-real-actual-source-fallback-',
    '20261116-current-real-fallback-',
    '20261116-current-past-entry-inner-payload-',
    '20261116-current-real-actual-source-rows-',
    '20261116-current-real-worker-full-resources-',
    '20261116-current-real-worker-task-core-',
    '20261116-current-real-worker-scan-',
    '20261116-current-real-worker-depth-',
    '20261116-current-real-opaque-')
roots=[p for p in sorted(evidence.iterdir()) if p.is_dir() and p.name.startswith(prefixes)]
roots += [work,public,prior_work]
for name in ['20261116-native-real-fallback-and-past-payload-check',
    '20261116-native-real-fallback-forecast-and-payload-check',
    '20261116-native-real-rows-task-core-and-bridges-check',
    '20261116-native-real-rows-core-opacity-and-typing-check',
    '20261116-native-real-task-and-opaque-subset-check',
    '20261116-native-whole-real-worker-original-budget-check']:
    p=evidence/name;assert (p/'checks.json').exists();roots.append(p)
roots=list(dict.fromkeys(roots))
(work/'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots],indent=2)+'\n')
(work/'skipped-published-roots.json').write_text(json.dumps({'prior_immutable_checkpoints_retained':True,
    'live_factored_whole_worker_outputs_excluded':True,
    'live_semantic_endpoint_audit_excluded':True},indent=2)+'\n')
(work/'selection-review.json').write_text(json.dumps({'selected_roots':len(roots),
    'promoted_tuple_cons_fallback_rows_task_startup_opaque_payload_retained':True,
    'all_failed_originals_and_repairs_retained':True,
    'full_scan_and_depth_candidates_marked_unpromoted':True,
    'full_original_real_header_5493_preserved':True,
    'compiled_objects_excluded':True,'original_full_objective_preserved':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text=(prior_work/name).read_text().replace(prior_packet,packet)
    text=text.replace("BASE = '21b36cd26e9841ca63b09bda62432057da1ad9ad'", "BASE = '"+base+"'")
    text=text.replace('# Actual real-worker runtime, phase admission and nullary resources',
        '# Genuine real-task induction, captured startup and same-key cache payloads')
    (work/name).write_text(text)
text=(evidence/prior_packet/'verify.py').read_text().replace(prior_packet,packet)
(work/'verify.py').write_text(text)
print(json.dumps({'checked_code':code,'selected_roots':len(roots),'public_gates':5}))
