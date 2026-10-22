import datetime
import hashlib
import json
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-physical-meaning'
package = here / 'signature-plan'
review_path, expected_review_sha = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
for path, pin in json.loads((package / 'pins.json').read_text()).items():
    data = (package / path).read_bytes()
    assert sha(data) == pin['sha256'], path
contracts = {}
for name, lines, expected in [
    ('context.lean.txt', 9, 'e77baf30cd10e1d276341600663386d30104b8c05116ff77218b24257d0927e6'),
    ('private-signature.lean.txt', 8, '61c92c549e600f5ce9285a5d28908ffb0e20f6f88bab404b4aba3bad8aff44ef'),
    ('proposed-signature.lean.txt', 16, '5e1823c8064b825c21dbaf859381835154e19a231093e8f6e74f839bafb2f73c')]:
    data = (package / name).read_bytes()
    assert sha(data) == expected and len(data.splitlines()) == lines
    assert b':= by' not in data and b'sorry' not in data
    contracts[name] = dict(path='signature-plan/' + name, sha256=expected, lines=lines)
cuts = 0
index = json.loads((package / 'source-index.json').read_text())
for item in index:
    raw = (root / item['path']).read_bytes()
    assert sha(raw) == item['source_sha256'] and raw == (package / item['snapshot']).read_bytes()
    for span in item['ranges']:
        excerpt = b''.join(raw.splitlines(True)[span['start'] - 1:span['end']])
        assert sha(excerpt) == span['sha256'] and excerpt == (package / span['snapshot']).read_bytes()
        cuts += 1
assert len(index) == 13 and cuts == 20
scope = json.loads((package / 'import-scope.json').read_text())
assert scope['sole_import'] == 'SourceCurrentAllocatedNativeContextCache'
for name, item in scope['nodes'].items():
    raw = Path(item['source']).read_bytes()
    assert sha(raw) == item['source_sha256'], name
    excerpt = b''.join(raw.splitlines(True)[:item['header_lines']])
    assert sha(excerpt) == item['header_sha256'] and excerpt == (package / item['snapshot']).read_bytes()
for name, path in scope['paths'].items():
    assert path[0] == scope['sole_import'] and path[-1] == name
    assert all(right in scope['nodes'][left]['imports'] for left, right in zip(path, path[1:]))
assert sha((here / review_path).read_bytes()) == expected_review_sha
output = here / 'root-signature-review.json'
assert not output.exists()
gate = dict(status='ROOT_ACCEPTED_FOR_BODY_PROPOSAL_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    public_theorem='MicroCFTA.SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning', contracts=contracts,
    root_read_all_33_declaration_lines_and_route_budget=True,
    independent_review=review_path, independent_review_sha256=expected_review_sha,
    live_api_sources=13, exact_api_cuts=20, import_header_nodes=len(scope['nodes']), import_paths=len(scope['paths']),
    same_source_facts_holds_admitted_model_and_literal_row=True,
    both_child_admission_and_all_ambient_physical_row_language_equality=True,
    complete_codec_derived_before_readback=True, private_helper_optional=True,
    allowed_private_helper='original_of_readback', target_lines=[90,150], hard_stop_lines=180,
    default_declaration_limits_and_all_linters_required=True,
    compiler_and_official_install_authorized=False, haskell_changes=False, whole_goal_complete=False)
output.write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(dict(status='PASS', declarations=33, source_proposal_only=True, gate_sha256=sha(output.read_bytes()))))
