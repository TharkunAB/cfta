from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261116-expanded-birth-and-actual-kept-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] for c in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert code != '201a254faee6436e9172581d526f5b1e0ce44889'
request_path = work / 'current-board-expanded-birth-request.json'
assert not request_path.exists()
request = {
    'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {
        'title': 'Whole-worker birth history and actual pending-bucket dependency closure proved',
        'text': (
            f'Checked Source {code}. For every actual optimized-worker output at the SAME original supplied work/recursive budgets, '
            'ExpandedBirthHistory retains every old expanded value/root/UF class. Each final stored fragment is identical at its input slot '
            'or avoids EVERY input expanded class. Genuine inner task.work and outer Nat-depth inductions cover tuple, fallback, rows, '
            'captured/selected return, prefix, parked restart, prepared scan, successful preparation and opaque children. '
            'The resource IH comes from the existing all-depth theorem. There is no future-output supplier, new engine or larger fuel. '
            'All retained outputs before later stops remain covered. Original resource5493/public906 headers and ALL prior owner bytes remain unchanged '
            'after three normal imports. '
            'The actual pending-bucket producer combines E and the earlier held history for the SAME output. Packet.pending and an ORIGINAL '
            'pending lookup put every raw bucket target, including aliases and duplicates, in ExpandedBirthKept. The set excludes input expanded '
            'classes and the held class, and is closed under stored-fragment holes for ANY actual final Roots map. Original isolation and '
            'Protected.classes derive final separation. No new closure or numeric-cut premise is assumed. The earlier chosen-level/piecewise '
            'reconstruction is unnecessary for this route and remains an unproved alternative audit. '
            'The REAL parked clear export also passes: actual Packet/chosen/parked-singleton prefix yields the full removed bucket, original '
            'uv lookup, pending inputs, separation and created isolation at the IMMEDIATE post-clear entry. It retains ALL indexed alias receipts, '
            'actual metadata/core/decision and the real eagerChild/OuterNarrow resumeWithNarrow depth+1 to depth equality at unchanged fuels. '
            'It does not identify the older visitor with the real worker. '
            'Boundary: current-pending lookup at worker entry is different from a historical bucket already removed there. Attach the actual clear '
            'to its immediate real suffix and the SAME final output; arbitrary later entry may already have expanded a removed target. '
            'Every-event attachment, actual same-position target compatibility/typing, final aliases, native domains, guards, ALL removed/parked '
            'obligations and completion of the SAME original partial root under ONE assignment remain open. The earlier one-arrow conditional '
            'recompletion already gives UF/all stored equations/one bucket with actual raw-target agreement; do not splice existential witnesses. '
            'Warm C/M meanings, two inherited Returned priors, four mixed clauses, pending Profile closure, full typing/depth/completeness, both '
            'preprocessing/LPO directions, lazy demand/order/multiplicity, exact sizes/count/weights/training, both rank inverses, host bounds and '
            'compiled Haskell correspondence remain in scope. '
            f'All FIVE public gates pass: {report["source_files"]} Source inventory files, {report["direct_audit_imports"]} Audit imports, '
            f'{report["individual_reports"]} explicit reports (537 standard/3 free), {report["independent_reports"]} independent, '
            f'{report["owner_resource_probes"]} resource/component probes (ALL136 original+71 additional), '
            f'{report["audited_theorems"]} declarations. Strict owner reports205 standard/2 free. Source/driver pins unchanged; serial8GiB/zero '
            'swap/original2M resource proof limit. These counts do not establish full API coverage. '
            'All failed typed-binder/context/linter/probe/HasHole attempts and exact repairs are preserved; failed modules receive no credit. '
            'No Haskell source changed and no reachable-source defect is claimed. EVERY future Haskell fix must appear in FINDINGS.md. '
            'Goal ACTIVE; origin/formalize publication explicitly authorized.'
        ),
    },
    'metadata': {
        'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'public_gates': 5, 'source_files': report['source_files'],
        'direct_audit_imports': report['direct_audit_imports'],
        'explicit_reports': report['individual_reports'],
        'independent_reports': report['independent_reports'],
        'resource_probes': report['owner_resource_probes'],
        'audited_declarations': report['audited_theorems'],
        'genuine_inner_task_work_birth_induction_proved': True,
        'outer_depth_strong_birth_proved': True,
        'actual_source_pending_bucket_dependency_closure_proved': True,
        'actual_immediate_real_clear_inputs_proved': True,
        'all_historical_same_output_attachment_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False,
    },
}
request_path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps(request))
