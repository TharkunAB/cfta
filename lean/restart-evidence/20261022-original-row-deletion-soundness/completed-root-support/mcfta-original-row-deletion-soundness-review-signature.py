import datetime
import hashlib
import json
import re
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-deletion-soundness'
package = here / 'signature-plan'
def sha(data):
    return hashlib.sha256(data).hexdigest()
pins = json.loads((package / 'pins.json').read_text())
assert isinstance(pins, list) and len(pins) == 61
for pin in pins:
    data = (package / pin['path']).read_bytes()
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes'], pin['path']
contracts = {}
for name, lines, expected in [
    ('context.lean.txt', 8, 'afe61fd9ff562d6b562bd7ccb2053afdd1528ac2711236a7d6447567034d2928'),
    ('proposed-signature.lean.txt', 36, 'fcf8cfe500c226bce7eca1c4a3f8475b49f39d5fb798ff7c795094fa9ad90426')]:
    data = (package / name).read_bytes()
    assert sha(data) == expected and len(data.splitlines()) == lines
    assert b':= by' not in data and b'sorry' not in data
    contracts[name] = dict(path='signature-plan/' + name, sha256=expected, lines=lines)
assert not (package / 'private-signature.lean.txt').exists()
cuts = 0
index = json.loads((package / 'source-index.json').read_text())
for item in index:
    raw = (root / item['path']).read_bytes()
    assert sha(raw) == item['source_sha256'] and raw == (package / item['snapshot']).read_bytes()
    for span in item['ranges']:
        excerpt = b''.join(raw.splitlines(True)[span['start'] - 1:span['end']])
        assert sha(excerpt) == span['sha256'] and excerpt == (package / span['snapshot']).read_bytes()
        cuts += 1
assert len(index) == 15 and cuts == 20
graph = json.loads((package / 'import-graph.json').read_text())
assert graph['direct_imports'] == ['MicroCFTA.SourceCurrentOriginalRowPhysicalMeaning']
assert len(graph['header_nodes']) == 52 and len(graph['targets']) == 13
for name, item in graph['header_nodes'].items():
    raw = (root / item['path']).read_bytes()
    assert sha(raw) == item['sha256'], name
    imports = re.findall(r'^import\s+(\S+)\s*$', raw.decode(), flags=re.M)
    assert imports == item['imports'], name
for name, path in graph['targets'].items():
    assert path[0] == graph['direct_imports'][0] and path[-1] == name
    assert all(right in graph['header_nodes'][left]['imports'] for left, right in zip(path, path[1:]))
review = here / 'signature-audit/review.md'
assert sha(review.read_bytes()) == 'd24cb9393d03aaf5aaff46d02d002db0edb16cd4d4fb2952ec3673517566bc85'
output = here / 'root-signature-review.json'
assert not output.exists()
gate = dict(status='ROOT_ACCEPTED_FOR_BODY_PROPOSAL_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    public_theorem='MicroCFTA.SourceCurrentOriginalRowDeletionSoundness.deletion_sound',
    contracts=contracts, root_read_all_44_declaration_lines_and_route_budget_and_20_api_cuts=True,
    independent_review='signature-audit/review.md', independent_review_sha256=sha(review.read_bytes()),
    live_api_sources=15, exact_api_cuts=20, import_header_nodes=52, import_paths=13,
    same_source_facts_holds_admitted_model_and_literal_rows=True,
    explicit_ranked_model_is_index_of_existing_edge_law=True,
    existing_completed_edge_law_contains_sound_and_complete=True,
    only_sound_projection_used=True, bounded_completeness_projection_used=False,
    rank_erasure_used=False, exact_final_heap_coherence_growth_and_residencies_required=True,
    both_tested_identity_inclusions_for_every_ambient=True,
    full_payload_equalities_derived_from_actual_identity_tests=True,
    new_execution_or_scan_language_claim=False, new_completeness_or_total_meet_oracle=False,
    private_helpers_allowed=[], target_lines=[90,140], hard_stop_lines=180,
    default_declaration_limits_and_all_linters_required=True,
    compiler_and_official_install_authorized=False, haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(dict(status='PASS', declarations=44, source_proposal_only=True,
    gate_sha256=sha(output.read_bytes()))))
