import ast
import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

audit = Path('/tmp/mcfta-pair-request-admission-preparation-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'root-preparation-read-scope.json')['complete_selected_source_read']
assert load(HERE / 'root-declaration-review.json')['local_induction'] == 'preserved'
archive(audit, 'checkpoint-preparation-audit')
prep = HERE / 'checkpoint-preparation'
full = HERE / 'full-preparation'
assert not full.exists()
full.mkdir()
facts = {'__H25_MODULE_NAME__': NAME,
    '__H25_PUBLIC_SPECS_JSON__': [['completed_admitted', 'theorem']],
    '__H25_SOURCE_HARD_STOP__': 180}
selected = {}
for filename in ['root-run-check.py', 'check-full-public.py', 'prepare-selected-full.py']:
    data = (prep / filename).read_text()
    for token, value in facts.items():
        if isinstance(value, list):
            data = data.replace(repr(token), repr(json.dumps(value)))
        else:
            data = data.replace(token, str(value))
    assert not re.search(r'__H25_[A-Z0-9_]+__', data)
    ast.parse(data)
    assert not (HERE / filename).exists()
    (full / filename).write_text(data)
    (HERE / filename).write_text(data)
    selected[filename] = dict(sha256=sha(full / filename), lines=len(data.splitlines()))
tail = (prep / 'diagnostic-tail.lean.txt').read_text().replace('__H25_MODULE_NAME__', NAME).replace('__H25_PUBLIC_SHORT__', 'completed_admitted')
assert len(tail.splitlines()) == 14 and not re.search(r'__H25_[A-Z0-9_]+__', tail)
(full / 'diagnostic-tail.lean.txt').write_text(tail)
(full / 'declaration-bindings.json').write_text(json.dumps(dict(exact_three_declaration_facts=facts,
    selected=selected), indent=2) + '\n')
report = dict(status='ROOT_ACCEPTED_DECLARATION_BOUND_FULL_TOOLS',
    observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_whole_early_full_sources_read=True, root_whole_original_tools_and_exact_verifier_delta_read=True,
    independent_source_review='CLEAR', selected_early_full_tools=selected, exact_declaration_facts=facts,
    composite_tool_lines=1024, composite_assertions=332,
    verifier_evidence_binding_still_pending=True, verifier_activated=False, new_proof_jobs=0,
    source_body_gate_pending=True, compiler_authorized=False)
save('root-full-tools-review.json', report)
print(json.dumps(report))
