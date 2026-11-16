from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = root / 'lean/restart-evidence/20261116-immediate-historical-suffix-kept-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5 and all(x['exit'] == 0 and not x['sorryAx'] and not x['nonstandard_axioms'] for x in report['checks'])
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == code
text = f'''Checked Source {code}. The new public runEager_real_parked_removed_bucket_kept_at_immediate_suffix attaches ONE actual removed bucket to EVERY output of its SAME original real eager run. Original Packet/Fits/Heap/mass/selector obligations, successor-depth eagerReserved, chosen expansion and actual parked singleton prefix suffice. The original six work fuels are unchanged. Actual clear and prefix APIs derive immediate pending/separation/isolation, Packet/resources and the real eagerChild/OuterNarrow predecessor-depth suffix. Exact run equality transports SAME output membership. Whole E and R then give all original raw-target membership and stored-fragment dependency closure under EVERY final Roots map, relative to that immediate post-clear state. No post-state/history/closure/model supplier, new numeric engine or larger fuel. Private frozen header passed without repair; public conversion changes only name/visibility. Every old owner byte remains after one normal import; old Audit bytes remain as prefix; all6183 other Source files remain byte-exact. No Haskell/runtime change.

Boundary: this is ONE authentic clear-event attachment, not EVERY historical event. Sibling scans reuse their captured enumeration cache; an earlier explored sibling does not supply a later output's history or aliases. The next causal route must retain the actual producing row, completed prefix, local output index/offset and its actual eager CPS child/callback ancestry, then the same recursive output. Frozen2d6af45b candidate derives the indexed actual prepared-eager row origin but is UNCOMPILED. The exact next callback-origin header2a0d5ae8 is UNPROVED and needs genuine CPS/list/height output-origin induction. Existing actual_prepared_child_raw_path_congruence already proves indexed same-position aliases after an actual prepared child; the historical association, final alias transport and source-role TypeIn typing remain open. Kept membership alone supplies neither compatibility nor typing. No duplicate conditional wrapper or cross-sibling claim was added.

Largest gap: ONE finite accepted completion of the SAME original partial root under ONE assignment satisfying current native domains/guards, UF, stored equations and EVERY removed/parked obligation on THAT causal branch. The earlier conditional same-snapshot arrow theorem supplies one assignment for UF/all stored equations/ONE bucket with actual target agreement; do not combine separate existential witnesses. Existing conditional ResourceHistory.render_sound remains valid at its explicit history/residual boundary. Warm C/M meanings, inherited Returned/mixed clauses, pending Profile closure and full typing/depth/completeness, preprocessing/LPO, order/multiplicity/lazy demand, exact sizes/count/weights/training, both rank inverses, host bounds and compiled Haskell correspondence remain in scope.

All FIVE gates pass: {report['source_files']} Source inventory files, {report['direct_audit_imports']} direct Audit imports, {report['individual_reports']} explicit reports ({report['checks'][-1]['axiom_groups']} standard/{report['checks'][-1]['axiom_free_reports']} free), {report['independent_reports']} independent reports, {report['owner_resource_probes']} resource/component probes (all136 original+72 additional), {report['audited_theorems']} audited declarations. Serial8GiB/zero swap/original2M resource proof limit; pins unchanged; no sorryAx/nonstandard axioms. Counts are not full API coverage or completion. No reachable-source defect or Haskell fix is claimed. EVERY future Haskell fix must be in FINDINGS.md. Goal ACTIVE; origin/formalize publication explicitly authorized.'''
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337', 'username': 'mcfta-lean-review',
    'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'One actual parked clear has same-output dependency closure', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': report['source_files'], 'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'], 'independent_reports': report['independent_reports'],
        'resource_probes': report['owner_resource_probes'], 'audited_declarations': report['audited_theorems'],
        'public_gates': 5, 'one_real_clear_same_original_output_kept_proved': True,
        'all_causal_historical_events_attached_proved': False, 'joint_historical_model_proved': False,
        'next_actual_eager_causal_row_origin_candidate_compiled': False, 'haskell_changed': False}}
path = work / 'current-board-historical-suffix-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
