from pathlib import Path
from datetime import datetime
import json
import uuid

work = Path(__file__).parent
report = json.loads((work.parent / '20261117-selected-row-and-prefix-publication/checked.json').read_text())
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert len(report['checks']) == 5 and all(c['exit'] == 0 and not c['nonstandard_axioms']
    and not c['diagnostics'] and not c['sorryAx'] for c in report['checks'])
at = datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
text = f"""[{at}] Source {code} proves both original actual-prefix contracts: 8cf8e7bc narrowed_marked_row_fields and b17f0034 runPrefix_program_slots. The first derives fields for THAT selected narrowed row from an original Packet, chosen step and genuine PAST ProgramSlots. The second preserves EXISTING marks through every cached parked/narrowed result of the actual runPrefix. Both retain all SIX independent original read/check/native/representative/index/callback fuels. No future PrefixValid, forecast, future field provider, alternate adequate run or changed runtime operation was introduced. Stopped/uncached tags make no future-cache claim. These theorems do not introduce fresh marks or propagate them through the complete recursive worker.

All five focused gates passed. Eight strict component reports are fresh (2 public, 6 private);366 earlier reports are inherited with committed archive, unchanged exact proof inputs and toolchain bindings reverified. The650 Audit and245 independent reports are fresh. There are6244 Source files and5244 ordinary Audit imports. No passing check has sorryAx, nonstandard axioms or diagnostics. All6241 earlier non-Audit Source files, including the large owner, are byte-exact. Proof limits remain unchanged. The first prefix check failed because SourcePruningNativeMeaning was not imported. Adding that ordinary import fixed every error without changing any old proof body or frozen header. All failed packets and repairs remain. Exact previews and real-host process checks preceded deletion of four terminal object directories (4,958,768bytes).

The frozen Haskell caller audit verifies31 source pins. Haskell initializes the persistent constrainedRecursion flag from its initial root; there is no public/default checkEmpty switch. The second per-query reachesConstrainedMu gate is already modeled in Lean. A raw original-root outer-gate specialization is still UNPROVED; reduced/refolded Space requires separate justification. A false conservative emptiness result does not prove native inhabitance. The only-U pending-type membership result is useful only after its actual source-derived premises are established. No reachable Haskell defect is claimed and no Haskell source changed. Every future Haskell fix belongs in root FINDINGS.md.

Next derive the chronological fresh Program marks, native Type/Marker class compatibility and the single finite accepted completion of the SAME original emitted root under ONE assignment satisfying ALL causal historical obligations. Program ValueFields has only empty/node cases. Ordinary Program children keep their full annotation bucket; the empty-bucket Mu/Union fallback is an annotation-child case. Do not assume scs=[] or invent a later U-arrow call across that deferred boundary. The full typing/depth/completeness/preprocessing/LPO/order/multiplicity/lazy-demand/exact-size/count/weights/training/rank/host/Haskell scope remains OPEN. Goal ACTIVE; only origin/formalize pushes authorized."""
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Actual six-fuel prefix source facts and existing Program marks', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': 6244, 'direct_audit_imports': 5244, 'explicit_reports': 650,
        'independent_reports': 245, 'fresh_component_reports': 8,
        'inherited_bound_component_reports': 366, 'public_gates': 5,
        'actual_six_fuel_selected_row_fields_proved': True,
        'actual_six_fuel_prefix_program_slots_proved': True,
        'whole_history_program_mark_production_proved': False,
        'source_type_marker_class_consistency_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-real-prefix-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
