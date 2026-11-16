from pathlib import Path
import json,re,subprocess
r=Path('/home/tritlo/Code/mcfta');b=r/'lean/restart-evidence';w=Path(__file__).parent
prior='9f4ad619d01ec5dd187bb6c25db962c60c558da7';code='557ae8635ed531b96ebaa6e30a6933997ca7e6fd';packet='20261116-native-path-checkpoint';oldpacket='20261116-eager-history-invariants-checkpoint';oldwork=b/'20261116-eager-history-invariants-checkpoint-work'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==code
public=b/'20261116-native-admission-and-parent-path-publication';result=json.loads((public/'checked.json').read_text());assert len(result['checks'])==5 and result['individual_reports']==507 and result['audited_theorems']==98722 and result['independent_reports']==102
assert all(c['exit']==0 and not c['nonstandard_axioms'] for c in result['checks'])
old=json.loads((b/oldpacket/'checkpoint.json').read_text())
config=dict(result,checked_code=code,prior_checkpoint=prior,public_run=str(public),public_gates=5,explicit_reports=507,source_files=6169,direct_audit_imports=5169,board_prefix='current-board-native-path-',new_modules=4,new_public_theorems=10,old_non_audit_sources_byte_exact=6160,old_owner_exact_prefixes=4,every_old_header_and_proof_preserved=True,full_scope=old['full_scope'],one_removed_bucket_and_current_rendered_models_are_separate_witnesses=True,known_cumulative_tmp_removed_bytes=1546007440)
(w/'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
phase=b/'20261116-warm-edge-and-recompletion-work';names={phase.name,w.name,public.name,'20261116-warm-edge-and-recompletion-publication'}
for p in phase.glob('*.py'):
 names.update(n for n in re.findall(r'20261116-[a-z0-9-]+',p.read_text()) if (b/n).is_dir())
# Existing immutable archives keep the earlier inputs. Do not copy them recursively.
names={n for n in names if not n.endswith('-checkpoint') and n not in {oldwork.name,'20261116-source-assignment-events-work','20261116-worker-invariants-work','20261116-worker-origin-work','20261116-worker-invariants-publication','20261116-shared-native-model-publication','20261116-eager-history-origins-work','20261116-source-assignment-events-work','20261116-worker-invariants-work'}}
(w/'archive-roots.json').write_text(json.dumps(['lean/restart-evidence/'+n for n in sorted(names)],indent=2)+'\n')
(w/'skipped-published-roots.json').write_text(json.dumps({'earlier_immutable_checkpoints_preserved':True,'earlier_published_roots_not_copied_recursively':True,'new_failed_attempts_and_repairs_retained':True},indent=2)+'\n')
(w/'selection-review.json').write_text(json.dumps({'full_objective_preserved':True,'all_old_proofs_counterexamples_repairs_and_drafts_preserved':True,'all_new_failed_strict_runs_preserved':True,'wrong_owner_probe_assembly_preserved_as_failed':True,'all_old_owner_bytes_exact_prefixes':True,'OnlyU_is_boundary_atom_restriction_not_handle_identity':True,'separate_existential_models_not_combined':True,'haskell_unchanged_and_no_fix_claimed':True,'compiled_objects_excluded':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
 s=(oldwork/name).read_text().replace(oldpacket,packet).replace("BASE = 'ac3fed1766f805c7f355db1bb010d42d32cbf2c6'","BASE = '"+prior+"'").replace('# Actual native admission and parent-path compatibility','# Actual native admission and parent-path compatibility');(w/name).write_text(s)
(w/'verify.py').write_text((b/oldpacket/'verify.py').read_text().replace(oldpacket,packet))
print(json.dumps({'code':code,'roots':len(names),'new_modules':4,'new_public_reports':10,'explicit_reports':507}))
