import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-language'
package = here / 'signature-plan'
def sha(data):
    return hashlib.sha256(data).hexdigest()
pins = json.loads((package / 'pins.json').read_text())
assert isinstance(pins, dict) and len(pins) == 85
for name, pin in pins.items():
    data = (package / name).read_bytes()
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes'], name
expected = [
    ('context.lean.txt', 18, 'c06a00d6a9daff81a2b460f516c6b28052afdbc7a3e5b63c6f845734fc463d64'),
    ('private-execute-yielded-add.lean.txt', 7, '36f9082d97a6b46ec650e7f23ecc8746a5b0500125f01d2484e7aaea1a7af758'),
    ('private-scan-boundary-complete.lean.txt', 68, '00d0e8ba43ede77f379a88e540540ea105713662a33ca9d525d05f26a77afb0a'),
    ('proposed-signature.lean.txt', 57, '5ba1182f613a4323a9e8e6f105018c1ee829bc5c0e79dc5caaeac215a397102d'),
    ('local-complete-statement.lean.txt', 36, 'aa415ae2fb4fb0e58a8c8ce1ba5ed4cb73229bf9853b3e612e408b80ed027e6e'),
    ('local-rows-binding.lean.txt', 1, '1ca635278f46c50ae752a4d523e1520838d3a080ee70f1a270c885e4eea96e06'),
    ('local-strong-IH-expanded.lean.txt', 38, 'c48b7641c04fa86342393163466473b5546906116a479745ed60dc65a8cb2a58')]
contracts = {}
for name, lines, digest in expected:
    data = (package / name).read_bytes()
    assert sha(data) == digest and len(data.splitlines()) == lines
    assert b':= by' not in data and b'sorry' not in data
    contracts[name] = dict(path='signature-plan/' + name, sha256=digest, lines=lines)
assert (package / 'private-execute-yielded-add.lean.txt').read_bytes() == (
    package / 'basis/H17-private-execute-yielded-add.lean.txt').read_bytes()
for selected, old, indent in [
    ('private-scan-boundary-complete.lean.txt', 'H17-private-scan-boundary-complete.lean.txt', 6),
    ('proposed-signature.lean.txt', 'H17-public-signature.lean.txt', 6),
    ('local-complete-statement.lean.txt', 'H17-local-complete-statement.lean.txt', 8)]:
    text = (package / selected).read_text()
    old_text = (package / 'basis' / old).read_text()
    marker = ' ' * indent + '∀ ambient : InternedGuardedLanguage.Env Symbol,'
    before, separator, _ = text.partition(marker)
    assert separator and before.endswith(' ∧\n')
    inverse = before[:-3] + '\n'
    inverse = inverse.replace('    (admitted : inputModel.valid (inputOf parent))\n', '')
    if inverse.startswith('/--'):
        inverse = old_text.split('\n', 1)[0] + '\n' + inverse.split('\n', 1)[1]
    assert inverse == old_text, selected
index = json.loads((package / 'source-index.json').read_text())
assert isinstance(index, list) and len(index) == 14
cuts = 0
for item in index:
    path = Path(item['path'])
    raw = (path if path.is_absolute() else root / path).read_bytes()
    assert sha(raw) == item['source_sha256'] and raw == (package / item['snapshot']).read_bytes()
    for span in item['ranges']:
        excerpt = b''.join(raw.splitlines(True)[span['start'] - 1:span['end']])
        assert sha(excerpt) == span['sha256'] and excerpt == (package / span['snapshot']).read_bytes()
        cuts += 1
assert cuts == 20
graph = json.loads((package / 'import-paths.json').read_text())
assert graph['candidate_imports'] == [
    'MicroCFTA.SourceCurrentOriginalRowClusterCompletion',
    'MicroCFTA.SourceCurrentOriginalRowDeletionSoundness']
for name, item in graph['actual_import_headers'].items():
    raw = (root / item['path']).read_bytes()
    assert sha(raw) == item['source_sha256'], name
    imports = re.findall(r'^import\s+(\S+)\s*$', raw.decode(), flags=re.M)
    assert imports == item['imports'], name
path = graph['public_FormulaEq_import_path']
assert path[0] in graph['candidate_imports'] and path[-1] == 'MicroCFTA.FormulaExecutable'
assert all(right in graph['actual_import_headers'][left]['imports'] for left, right in zip(path, path[1:]))
review = here / 'signature-audit/review.md'
assert sha(review.read_bytes()) == sys.argv[1]
output = here / 'root-signature-review.json'
assert not output.exists()
gate = dict(status='ROOT_ACCEPTED_FOR_BODY_PROPOSAL_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    public_theorem='MicroCFTA.SourceCurrentOriginalRowClusterLanguage.cluster_complete',
    contracts=contracts, root_read_all_declarations_local_statements_route_budget_and_20_api_cuts=True,
    independent_review='signature-audit/review.md', independent_review_sha256=sys.argv[1],
    live_api_sources=14, exact_api_cuts=20, all_H17_premises_and_outputs_retained_by_exact_inverse=True,
    same_source_facts_holds_admitted_model_ranked_input_and_literal_filtered_rows=True,
    actual_H15_common_middle_done_resident_full_edge_law_and_packet_used_once=True,
    actual_H19_sound_implications_from_same_middle_coherent_heap_and_composed_growth=True,
    candidate_first_drop_promotion_and_reversed_accumulator_union_invariant=True,
    all_ambient_finite_term_physical_kept_union_iff_original_symbol_group=True,
    all_existing_cache_extension_returned_idle_and_global_domain_trace_outputs_retained=True,
    genuine_initial_width_Room_and_initial_domain_Valid_remain_required=True,
    success_or_desired_language_or_per_comparison_Room_or_generated_parent_oracles=False,
    private_helpers_allowed=['execute_yielded_add', 'scan_boundary_complete'],
    local_strong_IH_complete_header_exposed=True, expanded_IH_review_only=True,
    target_lines=[410, 480], hard_stop_lines=500, all_actual_local_statements_comments_blanks_count=True,
    default_declaration_limits_and_all_linters_required=True,
    compiler_and_official_install_authorized=False, haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(dict(status='PASS', source_proposal_only=True, api_sources=14, cuts=20,
    gate_sha256=sha(output.read_bytes()))))
