exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import ast
import sys

owner = Path('/tmp/mcfta-scan-node-counter-growth-closing-preparation')
peer = Path(sys.argv[1])
checked_package(owner,'60a7f21625e1f5ef0cb83bb0bf3de44a135eb9d5b2509906eca7d85dd512eac8','9f3f51359f14cb79bc7a65f03833284c9fbac07d2c5762b2766a2e21a2f02ceb')
checked_package(peer,sys.argv[2],sys.argv[3])
assert sha(peer / 'review.json') == sys.argv[4] and load(peer / 'review.json')['status'] == 'CLEAR'
manifest = load(owner / 'selected-scripts.json')
recipe = load(owner / 'literal-recipe.json')
for name,pin in manifest.items():
    selected = owner / 'selected' / name
    assert sha(selected) == pin['selected']['sha256']
    assert len(selected.read_text().splitlines()) == pin['lines']
    assert sum(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(selected.read_text()))) == pin['assertions']
    adapted = (owner / 'basis' / name).read_text()
    for change in recipe['ordered_checkpoint_substitutions'][name]:
        assert adapted.count(change['before']) == change['occurrences']
        adapted = adapted.replace(change['before'],change['after'])
    assert adapted == (owner / 'pending-selected' / name).read_text()
    for span in reversed(recipe['data_binding_spans'][name]):
        assert adapted[span['pending_start']:span['pending_end']] == span['token']
        adapted = adapted[:span['pending_start']] + span['value'] + adapted[span['pending_end']:]
    assert adapted == selected.read_text()
    for span in reversed(recipe['data_binding_spans'][name]):
        assert adapted[span['selected_start']:span['selected_end']] == span['value']
        adapted = adapted[:span['selected_start']] + span['token'] + adapted[span['selected_end']:]
    assert adapted == (owner / 'pending-selected' / name).read_text()
    for change in reversed(recipe['ordered_checkpoint_substitutions'][name]):
        assert adapted.count(change['after']) == change['occurrences']
        adapted = adapted.replace(change['after'],change['before'])
    assert adapted == (owner / 'basis' / name).read_text()
    assert not (HERE / name).exists()
assert sum(pin['lines'] for pin in manifest.values()) == 236
assert sum(pin['assertions'] for pin in manifest.values()) == 59
assert (owner / 'selected/verify-seal.py').read_bytes() == (owner / 'basis/verify-seal.py').read_bytes()
binding = load(owner / 'binding-values.json')
assert binding['actual_proof_cut_pin']['sha256'] == sha(HERE / 'actual-proof-cut.json')
assert binding['root_history_review_pin']['sha256'] == sha(HERE / 'root-source-history-review.json')
for mode in ['normal','live']:
    assert load(HERE / ('proof-evidence-' + mode + '.json'))['status'] == 'PASS'
assert (HERE / 'current-update.md').is_file() and (ROOT / 'lean/notes-current-scan-node-counter-growth.md').is_file()
archive(owner,'closing-preparation')
archive(peer,'closing-actual-audit')
for name in manifest:
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
save('root-closing-tools-review.json', {
    'status':'ACCEPTED_WHOLE_CLOSING_SOURCES_AND_ACTUAL_BINDING','module':NAME,
    'root_complete_selected_lines_read':236,'selected_assertions':59,'selected_hard_stop':256,
    'root_complete_exact_literal_and_ten_data_span_inverses_read':True,
    'verify_seal_byte_identical':True,
    'independent_review_sha256':sha(peer / 'review.json'),
    'installed_tools':{name:pin['selected']['sha256'] for name,pin in manifest.items()},
    'checkpoint_execution_authorized':True,
    'support_requires_all_final_components_archived':True,
    'seal_requires_mandatory_final_checkpoint':True,
    'future_preservation_seal_and_push_not_claimed':True,'goal_status':'ACTIVE_INCOMPLETE'})
print('PASS: whole reviewed closing tools and all ten actual bindings installed.')
