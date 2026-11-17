from pathlib import Path
from datetime import datetime
import json
import uuid

work = Path(__file__).parent
report = json.loads((work.parent / '20261117-application-class-birth-publication/checked.json').read_text())
code = json.loads((work / 'SOURCE-COMMIT.json').read_text())['source_commit']
assert len(report['checks']) == 5 and all(c['exit'] == 0 and not c['nonstandard_axioms']
    and not c['diagnostics'] and not c['sorryAx'] for c in report['checks'])
at = datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
text = f'''[{at}] Source {code} proves the original 09764d59 application_class_birth declaration. One actual source-certified four-child CachedOwn.prepare singleton, PAST EdgeFields and StorageValid derive exact fresh slots n,n+1,n+2; unchanged UF forest; exact pending stores and singleton roots; pairwise distinct birth classes; ordered full trie paths; and the SAME staged inherited-plus-own buckets. The normalized classes are Type-layout [0]=[2,0,2], Marker-layout [1]=[2,0,0], Type-layout [2,0,1]=[3,0]. This is physical source class birth, not TypeIn or later semantic class separation. No TypeSlot premise, runtime operation, new resource provider, larger runtime fuel or changed first header was added. All original Source files except Audit remain exact.

All five focused publication gates pass. There is ONE fresh strict component report and365 inherited component reports whose committed archive, exact proof inputs and toolchain files were reverified. The648 Audit reports and243 independent reports were checked afresh. There are6242 Source files,5242 Audit imports and{report['audited_theorems']} audited declarations. The old large owner was not recompiled in the strict component gate because its entire source and inputs are unchanged. This distinction is explicit in the report;366 is the combined component evidence count. The two failed first checks and both local repairs remain. Ordered readback passed by CBV; the final bucket proof needed both Function.comp_def and Nat.zero_add. No passed check has sorryAx or a nonstandard axiom. All old limits remain; new proof uses original defaults. Temporary compiled objects were removed only after exact previews and real host process checks.

The next frozen8cf8e7bc selected-row-fields candidate derives THAT row's certificate from a PAST ProgramSlots certificate and the actual successful narrowed prefix at SIX INDEPENDENT supplied fuels. It is UNCOMPILED and has no theorem credit. Existing prepared_marked_fields already handles the later actual preparation, so no duplicate wrapper was added. Chronological production of Program marks through every actual entry remains open.

The new lineage audit identifies a real deferred-path boundary. A current source function component can have full Mu U at its annotation. A nonterminal Mu/Union child can return a fresh hole storing bucket[], so that tuple does not execute a nested U-arrow Marker child. The old n+1 path is present at the actual dispatch input, not automatically at a later invented arrow call. Follow the retained historical obligation through parked recompletion. For a genuine terminal annotation, the next occurrence link is SAME IncomingNode.finish descendants write to SAME later selected-preparation read and arrow invocation. Generic conditional terminal aliases and generic descent composition are already available and do not produce that genealogy.

The full goal remains ONE finite accepted completion of the SAME original source root under ONE compatible assignment, satisfying actual native domains, proper paths, UF, residuals, stored equations, readback, parked recompletion and EVERY causal historical obligation. Keep all original budgets, noStop and outputs before later stops, plus the full typing/depth/completeness/preprocessing/LPO/order/multiplicity/lazy-demand/exact-size/count/weights/training/rank/host/Haskell contracts. Source role transport, later compatibility and the one-model conclusion remain OPEN. No accepted-source collision or Haskell defect is claimed. No Haskell source changed; EVERY future Haskell fix belongs in root FINDINGS.md. Goal ACTIVE; origin/formalize pushes authorized.'''
request = {'thread_id': '1c1333d7-46ea-4f46-a9a1-b5d13e577337',
    'username': 'mcfta-lean-review', 'post_type': 'note', 'request_id': str(uuid.uuid4()),
    'content': {'title': 'Exact actual application class births and the deferred-path boundary', 'text': text},
    'metadata': {'project': 'mcfta', 'branch': 'formalize', 'source': code,
        'source_files': 6242, 'direct_audit_imports': 5242, 'explicit_reports': 648,
        'independent_reports': 243, 'fresh_component_reports': 1,
        'inherited_bound_component_reports': 365, 'public_gates': 5,
        'application_class_birth_proved': True, 'original_0976_header_exact': True,
        'source_to_arbitrary_current_row_fields_proved': False,
        'source_type_marker_class_consistency_proved': False,
        'joint_historical_model_proved': False, 'haskell_changed': False}}
path = work / 'current-board-app-birth-request.json'
assert not path.exists(), 'Reuse the exact durable request for retries'
path.write_text(json.dumps(request, indent=2) + '\n')
print(json.dumps({'request_file': str(path), 'request_id': request['request_id'], 'source': code}))
