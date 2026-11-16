from pathlib import Path
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
work=Path(__file__).parent
evidence=root/'lean/restart-evidence'
packet='20261116-real-worker-assembly-checkpoint'
prior_packet='20261116-identity-any-budget-checkpoint'
prior_work=evidence/'20261116-identity-any-budget-checkpoint-work'
base='21b36cd26e9841ca63b09bda62432057da1ad9ad'
code='70d6b1041fcad9786a63c5d437b9ae3e55d1fe2e'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==code
public=evidence/'20261116-real-worker-assembly-publication'
result=json.loads((public/'checked.json').read_text())
assert len(result['checks'])==5
assert all(x['exit']==0 and not x['nonstandard_axioms'] for x in result['checks'])
config=dict(result,checked_code=code,prior_checkpoint=base,public_run=str(public),
    public_gates=5,explicit_reports=424,source_files=6128,direct_audit_imports=5128,
    board_prefix='current-board-public-',new_modules=2,new_public_theorems=2,
    unchanged_receipt_proofs_made_public=3,
    old_non_audit_sources_byte_exact=6123,
    old_owner_and_audit_bytes_preserved_as_exact_blocks=True,
    original_c831_declaration='c831a364518a5fb5e9bce2008227efe44cd693e7c10442ad4eaa0c12f2b0ec8a',
    identity_theorem_scope='Identity narrowing, Metadata Unit, empty templates, stop none, default order, same original workFuel/recursiveFuel and every emitted output.',
    native_CM_query_scope='One literal initial node query; both complete memo families initially empty.',
    full_scope='One finite accepted completion of same original emitted partial root under ONE compatible assignment, including domains, paths, UF aliases, residuals, readback, parked recompletion and EVERY removed historical obligation on that branch; preserve original source/root/noStop, inputs, fuels, budgets and ALL emissions before later stops.')
(work/'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
prefixes=('20261116-current-real-actual-task-runtime-',
    '20261116-current-real-prefix-admission-',
    '20261116-current-real-nullary-captured-frame-',
    '20261116-current-real-actual-source-tuple-nil-',
    '20261116-current-real-actual-source-tuple-cons-')
roots=[]
for p in sorted(evidence.iterdir()):
    if p.is_dir() and p.name.startswith(prefixes) and any((p/n).exists() for n in ['MANIFEST.sha256','MANIFEST.json']):
        roots.append(p)
roots += [work,public,prior_work]
for name in ['20261116-native-real-task-runtime-and-nullary-check',
    '20261116-native-real-runtime-and-prefix-admission-check',
    '20261116-native-real-prefix-admission-le-trans-check',
    '20261116-native-real-source-tuple-nil-and-cons-check',
    '20261116-native-real-source-tuple-instance-and-config-check']:
    p=evidence/name
    assert (p/'checks.json').exists()
    roots.append(p)
roots=list(dict.fromkeys(roots))
(work/'archive-roots.json').write_text(json.dumps([str(p.relative_to(root)) for p in roots],indent=2)+'\n')
(work/'skipped-published-roots.json').write_text(json.dumps({'prior_immutable_checkpoints_retained':True,
    'unfinished_agent_packets_and_live_compiler_outputs_excluded':True},indent=2)+'\n')
(work/'selection-review.json').write_text(json.dumps({'selected_roots':len(roots),
    'runtime489_nullary272_admission252_promoted':True,
    'old_failed_parents_retained':True,'nullary_pattern_alpha_rename_explicit':True,
    'two_runtime_header_width_annotations_explicit':True,
    'three_receipt_visibility_exports_keep_type_and_proof_bytes':True,
    'tuple_candidates_unpromoted':True,'terminal_22694_failed_four_elaboration_sites':True,
    'terminal_25171_passed_101_probes_at_same_source':True,
    'compiled_objects_excluded':True,'original_full_objective_preserved':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text=(prior_work/name).read_text().replace(prior_packet,packet)
    text=text.replace("BASE = '8154da8fc57ef6e032862467eaac32d82ea7ad5b'", "BASE = '"+base+"'")
    text=text.replace('# Whole identity-worker resources at the original supplied budgets',
        '# Actual real-worker runtime, phase admission and nullary resources')
    (work/name).write_text(text)
text=(evidence/prior_packet/'verify.py').read_text().replace(prior_packet,packet)
(work/'verify.py').write_text(text)
print(json.dumps({'checked_code':code,'selected_roots':len(roots),'public_gates':5}))
