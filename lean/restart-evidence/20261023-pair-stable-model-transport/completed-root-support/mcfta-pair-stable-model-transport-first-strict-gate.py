import ast
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
PREP = HERE / 'checkpoint-preparation'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

packages = [
    ('checkpoint-preparation-audit', 'ed486540ec4d207bb2a9490c1d651b7759e8037a2b648e911714baf5a16b2dfe', 90, '6b7d3bc17505ccacdf4b234c650e1fcb1dbf4f5297982ab434cb7779f86c0c95'),
    ('schema-erratum', '00b8fb10e75485c11a0ed5588ab06228cb237cfe2333ee881efb5255bc14e926', 4, '8c841f7f03900ddfb88cfd170e38beb5f9709811695a28b6a01da9f483cb498a'),
    ('source', '8d6078b7070442e984fad7223aa45b452da8ade506914101a1e76ef4a87878d9', 61, '0aeb616e8b20de0cb46ce26bd3610bc2c0ea641df4fd2d9d94e8f510388a6e23'),
    ('body-audit', 'bc62fe62279e59b4411eb6d7ec5bb6782395f04dc58c52a546f9ebf2bc676f0a', 66, 'f57c76e17d9735f8f4a65a418fbd1834ce26ff41298420d1ffd2df99a73600be'),
]
for name, expected, count, freeze in packages:
    package = Path('/tmp/mcfta-pair-stable-model-transport-' + name)
    assert sha(package / 'pins.json') == expected and sha(package / 'FROZEN.json') == freeze
    pins = json.loads((package / 'pins.json').read_text())
    if isinstance(pins, dict):
        pins = [dict(path=path, **pin) for path, pin in pins.items()]
    assert isinstance(pins, list) and len(pins) == count
    for pin in pins:
        path = package / pin['path']
        assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(package), name], check=True)
tool_review = json.loads((HERE / 'checkpoint-preparation-audit/review.json').read_text())
assert tool_review['status'] == 'CLEAR' and tool_review['remaining_blockers'] == []
before = json.loads((HERE / 'schema-erratum/head-metrics-schema.before.json').read_text())
after = json.loads((HERE / 'schema-erratum/head-metrics-schema.json').read_text())
assert before == json.loads((PREP / 'schemas/head-metrics-schema.json').read_text())
assert before.pop('slice_pattern') == 'public-readback/original-row-reconstruction-{short}-{public-type,printed-public-type,body,axioms}.txt'
assert after.pop('slice_pattern') == 'public-readback/pair-stable-model-transport-{short}-{public-type,printed-public-type,body,axioms}.txt'
assert before == after
name = 'SourceCurrentSameSymbolEdgeModelTransport'
facts = {'__H24_MODULE_NAME__': name, '__H24_PUBLIC_SPECS_JSON__': [['rebase', 'theorem']], '__H24_SOURCE_HARD_STOP__': 120}
full = HERE / 'full-preparation'
full.mkdir()
selected = {}
for filename in ['root-run-check.py', 'check-full-public.py', 'prepare-selected-full.py']:
    data = (PREP / filename).read_text()
    for token, value in facts.items():
        if isinstance(value, list):
            data = data.replace(repr(token), repr(json.dumps(value)))
        else:
            data = data.replace(token, str(value))
    assert not re.search(r'__H24_[A-Z0-9_]+__', data)
    ast.parse(data)
    assert not (HERE / filename).exists()
    (full / filename).write_text(data)
    (HERE / filename).write_text(data)
    selected[filename] = dict(sha256=sha(full / filename), lines=len(data.splitlines()))
tail = (PREP / 'diagnostic-tail.lean.txt').read_text().replace('__H24_MODULE_NAME__', name).replace('__H24_PUBLIC_SHORT__', 'rebase')
assert len(tail.splitlines()) == 14 and not re.search(r'__H24_[A-Z0-9_]+__', tail)
(full / 'diagnostic-tail.lean.txt').write_text(tail)
(full / 'declaration-bindings.json').write_text(json.dumps(dict(exact_three_declaration_facts=facts, selected=selected), indent=2) + '\n')
tool_gate = dict(status='ROOT_ACCEPTED_DECLARATION_BOUND_FULL_TOOLS',
    observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_whole_early_full_sources_read=True, root_whole_original_tools_and_exact_verifier_delta_read=True,
    independent_source_review='CLEAR', selected_early_full_tools=selected, exact_declaration_facts=facts,
    composite_tool_lines=1005, composite_assertions=327, selected_schema_overlay='schema-erratum/head-metrics-schema.json',
    verifier_evidence_binding_still_pending=True, verifier_activated=False, new_proof_jobs=0)
(HERE / 'root-full-tools-review.json').write_text(json.dumps(tool_gate, indent=2) + '\n')
source = HERE / 'source' / (name + '.lean')
data = source.read_bytes()
assert sha(source) == '69a294d6519b9029480175702b8025b1b1a32a1d2328e3c24b6ad0916972610f'
assert len(data.splitlines()) == 41 <= 120
assert data.startswith((HERE / 'signature-plan/context.lean.txt').read_bytes())
header = (HERE / 'signature-plan/public-header.lean.txt').read_bytes().rstrip(b'\n') + b' := by\n'
assert data.count(header) == 1
assert not re.search(rb'(?m)^\s*set_option|\bsorry\b|\baxiom\b|\bprivate\b|\bhave\b|\binduction\b', data)
assert re.findall(rb'(?m)^theorem (\w+)', data) == [b'rebase']
assert sha(HERE / 'body-audit/review.md') == '3aea35edd637858f611355ded3043ce36fc255230352275d1457c25553454d27'
report = dict(status='ROOT_ACCEPTED_FOR_FIRST_STRICT', observed_at=datetime.datetime.now().astimezone().isoformat(),
    source='source/' + name + '.lean', source_sha256=sha(source), source_lines=41, hard_stop=120,
    shorter_than_target_accepted_without_padding=True, root_read_complete_source=True,
    independent_complete_source_review='CLEAR', independent_review_sha256=sha(HERE / 'body-audit/review.md'),
    exact_context_and_public_header=True, no_private_or_local_typed_obligations=True,
    first_strict_authorized=True, official_install_authorized=False, new_proof_jobs=0, whole_goal_complete=False)
(HERE / 'root-source-compile-gate.json').write_text(json.dumps(report, indent=2) + '\n')
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Complete source and early tools accepted\n\nRoot and independent source reviews pass for all twelve pending tools and the complete41-line proof.\nOnly the declaration-bound reader, materializer and unchanged capped runner are active.\nThe separate one-field schema erratum is selected. The original preparation remains immutable.\nThe first metadata archive rejected a dictionary assumption for the list manifest.\nThe corrected retry passed. Both attempts remain; neither is a proof job.\nThe first strict command is authorized. Official installation and actual evidence binding remain pending.\nThe whole goal remains ACTIVE.\n')
print(json.dumps(report))
