exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import ast
import string
import sys

mode, peer_path, peer_pins, peer_freeze, peer_review = sys.argv[1:]
facts = {
    'publication':('51cd07e5a136bb585f79c1a591f406cbf01f4eeef67860d5a4b08abb7a9de230','e22ab60f7a525a9a65a6836139c33811cd7862ffb80236026ceac4370f49195a',101,44,111,'publication-audit'),
    'document':('3f5806dea0ea9203986bac3539029b4331170038b0a29c2801889d24c26972ad','fd4d2a77384c3312ce4ec0ab9897f741884139f102164e52634e89cd45040ebf',88,25,98,'document-source-audit')}
owner_pins, owner_freeze, lines, assertions, hard, peer_archive = facts[mode]
owner = Path('/tmp/mcfta-scan-node-counter-growth-' + mode + '-preparation')
peer = Path(peer_path)
checked_package(owner,owner_pins,owner_freeze)
checked_package(peer,peer_pins,peer_freeze)
assert sha(peer / 'review.json') == peer_review and load(peer / 'review.json')['status'] == 'CLEAR'
manifest = load(owner / 'selected-scripts.json')
recipes = load(owner / 'literal-recipe.json')['recipes']
for name,pin in manifest.items():
    selected = owner / 'selected' / name
    assert sha(selected) == pin['sha256'] and len(selected.read_text().splitlines()) == pin['lines']
    assert sum(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(selected.read_text()))) == pin['assertions']
    adapted = (owner / 'basis' / name).read_text()
    for change in recipes[name]:
        assert adapted.count(change['from']) == change['occurrences']
        adapted = adapted.replace(change['from'],change['to'])
    assert adapted == selected.read_text()
    for change in reversed(recipes[name]):
        assert adapted.count(change['to']) == change['occurrences']
        adapted = adapted.replace(change['to'],change['from'])
    assert adapted == (owner / 'basis' / name).read_text()
    assert not (HERE / name).exists()
assert sum(pin['lines'] for pin in manifest.values()) == lines
assert sum(pin['assertions'] for pin in manifest.values()) == assertions
if mode == 'document':
    for name in ['current-update.template.md','focused-note.template.md']:
        template = (owner / name).read_text()
        assert template.endswith('\n') and '\r' not in template
        fields = {field for _,field,_,_ in string.Formatter().parse(template) if field is not None}
        assert fields <= {'now','proof','proof_short'}
    assert 'H6 constructed_node_calls remains strongest combined.' in (owner / 'focused-note.template.md').read_text()
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
archive(owner,mode + '-preparation')
archive(peer,peer_archive)
for name in manifest:
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
save('root-' + mode + '-review.json', {
    'status':'ACCEPTED_COMPLETE_SELECTED_' + mode.upper() + '_SOURCE', 'module':NAME,
    'root_whole_selected_source_lines_read':lines, 'selected_assertions':assertions,
    'selected_hard_stop':hard, 'root_whole_exact_recipes_and_inverse_deltas_read':True,
    'root_complete_both_template_payloads_read':mode == 'document',
    'independent_review_sha256':peer_review,
    'installed_tools':{name:pin['sha256'] for name,pin in manifest.items()},
    'standalone_requires_accepted_final_verifier':True,
    'proof_commit_and_documents_require_actual_dual_PASS_reports':True,
    'publisher_requires_final_document_review_support_and_verified_seal':True,
    'network_commands_authorized_in_selected_tools':False,
    'future_stage_success_claimed':False,'goal_status':'ACTIVE_INCOMPLETE'})
print('PASS: reviewed ' + mode + ' sources installed with unchanged runtime prerequisites.')
