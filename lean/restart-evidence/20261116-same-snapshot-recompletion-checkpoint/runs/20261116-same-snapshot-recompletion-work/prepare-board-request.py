from pathlib import Path
import json
import subprocess
import uuid

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261116-same-snapshot-recompletion-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] for c in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert code != '21a2175fc27a8015504094f901d3dd81f23b49d5'
request_path = work / 'current-board-recompletion-request.json'
assert not request_path.exists()
request = {
    'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {
        'title': 'Same-snapshot arrow recompletion is checked; whole-worker dependency producer remains open',
        'text': (
            f'Checked Source {code}. The original outer906 all-budget held-history theorem remains proved with its exact original header. '
            'New conditional theorem recomplete_arrow_bucket_at_snapshot constructs ONE explicit assignment at ONE final snapshot: '
            'UF, ALL stored fragment equations, ONE removed arrow bucket including indexed duplicates, actual target-value agreement, '
            'kept-value agreement and every separate pending value. It uses the actual target terms, not independent existential witnesses. '
            'Its local premises still include target typing, same-position compatibility and a dependency-closed kept set separate from the owner. '
            'These are not new assumptions of a global source theorem. Supporting lemmas prove same-fuel evaluator congruence, stored-equation '
            'fixed points, an explicit UF/stored-equation evaluation witness and a stratification-cut dependency lemma. '
            'The actual SAME-fuel child/finalizer producer now retains ONE chosen final ordering, fixes old expanded levels, and proves '
            'nondecrease for EVERY old allocated raw variable including eliminated aliases, actual write origins, and fragment avoidance '
            'of every old expanded class. Its premises are the original Packet/Ready/pending lookup/actual ChildInputs/chosen input ordering/finalizer result; '
            'there is no future cut, protection or model supplier. '
            'The missing source lift is whole-worker ordering transport or equivalent actual write provenance, plus actual raw-target occurrence '
            'compatibility and final alias transport. Use the chosen original frontier as cut. Exclude held by UF class; it need not have a lower final level. '
            'Direct fragment avoidance plus an unrelated Packet.ordered witness does not prove transitive evaluator noninterference. '
            'Current native domains, residual guards, EVERY earlier removed/parked obligation and completion of the SAME original root under '
            'that ONE assignment remain open. Warm C/M meanings, two inherited Returned priors, four mixed clauses, pending Profile closure, '
            'typing/depth/completeness, both preprocessing/LPO directions, lazy demand/order/multiplicity, exact sizes/count/weights/training, '
            'both rank inverses, host bounds and compiled Haskell correspondence remain in scope. '
            f'All FIVE public gates pass: {report["source_files"]} Source files, {report["direct_audit_imports"]} Audit imports, '
            f'{report["individual_reports"]} explicit reports (527 standard/3 free), {report["independent_reports"]} independent, '
            f'{report["owner_resource_probes"]} resource/component probes (all136 original+42 additional), '
            f'{report["audited_theorems"]} declarations. Serial8GiB/zero swap/original2M resource proof cap; source/driver pins unchanged. '
            'All prior owner bytes remain after ordinary imports. Failed untyped-binder and unresolved-HasHole attempts and exact repairs are preserved; '
            'failed modules receive no credit. No Haskell source changed and no reachable-source defect is claimed. '
            'EVERY future Haskell fix must be recorded in FINDINGS.md. Goal ACTIVE; origin/formalize publication explicitly authorized.'
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
        'conditional_same_snapshot_arrow_recompletion_proved': True,
        'actual_finalizer_allocated_monotonicity_proved': True,
        'whole_worker_dependency_cut_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False,
    },
}
request_path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps(request))
