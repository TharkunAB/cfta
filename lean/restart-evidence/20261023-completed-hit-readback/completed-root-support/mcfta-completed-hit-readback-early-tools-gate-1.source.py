import ast
import datetime
import re
import runpy
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

preparation = load(HERE / 'root-preparation-review.json')
declaration = load(HERE / 'root-declaration-review.json')
assert preparation['status'] == 'ROOT_PENDING_TOOLS_REVIEW_CLEAR_WITH_EXACT_FRAGMENT_STOP'
assert preparation['root_whole_program_read'] is True
assert preparation['lines'] == 1006 and preparation['static_ast_assertions'] == 325
assert declaration['status'] == 'ROOT_DECLARATION_REVIEW_CLEAR'
assert declaration['local_induction']['helper'] == 'ret_checked'
assert declaration['public_names'] == ['completed_hit_checked']
assert declaration['private_names'] == ['yielded_done', 'ret_checked']
prep = HERE / 'checkpoint-preparation'
full = HERE / 'full-preparation'
assert not full.exists()
full.mkdir()
facts = {'__H27_MODULE_NAME__': NAME,
    '__H27_PUBLIC_SPECS_JSON__': [['completed_hit_checked', 'theorem']],
    '__H27_SOURCE_HARD_STOP__': 180,
    '__H27_PRIVATE_NAMES_JSON__': ['yielded_done', 'ret_checked']}
selected = {}
for filename in ['root-run-check.py', 'check-full-public.py', 'prepare-selected-full.py']:
    data = (prep / filename).read_text()
    for token, value in facts.items():
        if isinstance(value, list):
            data = data.replace(repr(token), repr(json.dumps(value)))
            data = data.replace('"' + token + '"', repr(json.dumps(value)))
        else:
            data = data.replace(token, str(value))
    assert not re.search(r'__H27_[A-Z0-9_]+__', data)
    ast.parse(data)
    for target in [full / filename, HERE / filename]:
        assert not target.exists()
        target.write_text(data)
    selected[filename] = dict(sha256=sha(full / filename), lines=len(data.splitlines()))
tail = (prep / 'diagnostic-tail.pending.lean.txt').read_text().replace('__H27_MODULE_NAME__', NAME).replace('__H27_PUBLIC_SHORT__', 'completed_hit_checked')
assert len(tail.splitlines()) == 14 and not re.search(r'__H27_[A-Z0-9_]+__', tail)
(full / 'diagnostic-tail.lean.txt').write_text(tail)
(full / 'declaration-bindings.json').write_text(json.dumps(dict(exact_four_declaration_facts=facts,
    selected=selected), indent=2) + '\n')
report = dict(status='ROOT_ACCEPTED_DECLARATION_BOUND_FULL_TOOLS',
    observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_whole_early_full_sources_read=True, root_whole_pending_tools_read=True,
    independent_source_review='CLEAR', selected_early_full_tools=selected,
    exact_declaration_facts=facts, pending_tool_lines=1006, pending_assertions=325,
    exact_declaration_verifier_overlay_still_required=True,
    verifier_evidence_binding_still_pending=True, verifier_activated=False,
    new_proof_jobs=0, source_body_gate_pending=True, compiler_authorized=False)
save('root-full-tools-review.json', report)
print(json.dumps(report))
