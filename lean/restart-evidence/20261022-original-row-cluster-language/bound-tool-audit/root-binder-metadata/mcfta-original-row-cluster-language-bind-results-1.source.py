import ast
import difflib
import hashlib
import json
import re
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-language')
strict, full, audit = sys.argv[1:]
def sha(data):
    return hashlib.sha256(data).hexdigest()
def load(path):
    return json.loads((here / path).read_text())
assert load(audit + '.json')['exit_code'] == 0
audit_raw = (here / (audit + '.log')).read_bytes()
build = re.search(r'Build completed successfully \((\d+) jobs\)\.', audit_raw.decode())
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit_raw.decode())
assert build and dependencies and not re.search(r'\berror(?:\([^)]*\))?:', audit_raw.decode())
jobs = {}
for path in sorted(here.glob('*.json')):
    item = json.loads(path.read_text())
    if not isinstance(item, dict) or 'wrapper' not in item or 'exit_code' not in item:
        continue
    if Path(item.get('command', [''])[0]).name not in {'lean', 'lake'}:
        continue
    raw = (here / item['log']).read_bytes()
    errors = len(re.findall(r'^.+?:\d+:\d+: error(?:\([^)]*\))?:', raw.decode(), re.M))
    warnings = len(re.findall(r'^.+?:\d+:\d+: warning(?:\([^)]*\))?:', raw.decode(), re.M))
    jobs[path.stem] = [item['exit_code'], item.get('sha256'), sha(raw), errors, warnings]
assert {strict, full, audit} <= set(jobs)
assert jobs[strict][0] == jobs[full][0] == jobs[audit][0] == 0
selected = (here / (strict + '.source.lean')).read_bytes()
source_sha = sha(selected)
assert jobs[strict][1] == source_sha and (here / (strict + '.log')).read_bytes() == b''
assert jobs[strict][3:] == jobs[full][3:] == [0, 0]
name = 'SourceCurrentOriginalRowClusterLanguage'
assert selected == (here / 'source-proposal-v2' / (name + '.lean')).read_bytes()
variants = []
for path, reason in [
    ('source-proposal/' + name + '.lean', 'Initial complete proposal; strict1 returned one unused-simp warning.'),
    ('source-proposal-v2/' + name + '.lean', 'Remove only the unused or_comm argument; selected clean strict input.'),
    (name + '.lean', 'Exact selected math source retained by the public printer materializer')]:
    data = (here / path).read_bytes()
    variants.append(dict(path=path, sha256=sha(data), lines=len(data.splitlines()), reason=reason))
for stem, row in jobs.items():
    if row[1] and 'public' not in stem:
        data = (here / (stem + '.source.lean')).read_bytes()
        assert any(item['sha256'] == sha(data) for item in variants)
        variants.append(dict(path=stem + '.source.lean', sha256=sha(data),
            lines=len(data.splitlines()), reason='Exact actual ordinary-check input: ' + stem))
artifact_paths = {'source-proposal/H17-to-proposal.patch', 'source-proposal/note.md',
    'source-proposal/metadata-preflight-diagnostic.md', 'source-proposal-v2/note.md',
    'source-proposal-v2/warning-repair.patch', 'root-signature-review.json',
    'root-source-precheck.json', 'root-source-precheck-v2.json',
    'source-proposal-audit/review.md', 'source-proposal-v2-audit/review.md'}
for path in (here / 'source-proposal-v2/stopped-full-activation-metadata').iterdir():
    if path.is_file():
        artifact_paths.add(str(path.relative_to(here)))
for stem, row in jobs.items():
    artifact_paths.update(stem + suffix for suffix in ['.json', '.log', '.limits.json', '.usage.json'])
    if row[1] and 'public' in stem:
        artifact_paths.add(stem + '.source.lean')
contracts = load('root-signature-review.json')['contracts']
assert list(contracts) == ['context.lean.txt', 'private-execute-yielded-add.lean.txt',
    'private-scan-boundary-complete.lean.txt', 'proposed-signature.lean.txt',
    'local-complete-statement.lean.txt', 'local-rows-binding.lean.txt', 'local-strong-IH-expanded.lean.txt']
artifact_paths.update(item['path'] for item in contracts.values())
artifacts = [dict(path=path, sha256=sha((here / path).read_bytes()),
    bytes=len((here / path).read_bytes())) for path in sorted(artifact_paths)]
before_path, after_path = ['source-proposal' + suffix + '/' + name + '.lean' for suffix in ['', '-v2']]
patch_path = 'source-proposal-v2/warning-repair.patch'
patch = dict(before=before_path, after=after_path, path=patch_path,
    sha256=sha((here / patch_path).read_bytes()), fromfile='V1/' + name + '.lean',
    tofile='V2/' + name + '.lean', reason='Remove the sole unused simp argument reported by actual strict1; keep the promotion argument.')
expected_patch = ''.join(difflib.unified_diff((here / before_path).read_text().splitlines(True),
    (here / after_path).read_text().splitlines(True), fromfile=patch['fromfile'], tofile=patch['tofile']))
assert expected_patch == (here / patch_path).read_text()
history = dict(status='ROOT_ACCEPTED', selected_source_sha256=source_sha,
    variants=variants, artifacts=artifacts, patches=[patch], rejected_public_types=[])
report = load('public-readback/original-row-cluster-language-full-readback.json')
head = report['heads'][0]
checked = (here / 'public-readback/original-row-cluster-language-cluster_complete-public-type.txt').read_bytes()
body = (here / 'public-readback/original-row-cluster-language-cluster_complete-body.txt').read_bytes()
assert report['source_sha256'] == source_sha and report['log_sha256'] == jobs[full][2]
metrics = dict(ACTUAL_JOBS=len(jobs), SOURCE_JOBS=sum(bool(row[1]) for row in jobs.values()),
    AUDIT_JOBS=sum(not row[1] for row in jobs.values()), FAILED_JOBS=sum(row[0] != 0 for row in jobs.values()),
    WARNED_SOURCE_EXIT_ZERO_JOBS=sum(row[0] == 0 and bool(row[1]) and bool(row[4]) for row in jobs.values()),
    REJECTED_PUBLIC_TYPE_JOBS=0, AUDIT_BUILD_JOBS=int(build.group(1)), AUDIT_DEPENDENCIES=int(dependencies.group(1)))
values = {**metrics, 'SELECTED_SOURCE_SHA': source_sha, 'SOURCE_SHA': source_sha, 'SOURCE_LINES': len(selected.splitlines()),
    'SELECTED_STRICT_STEM': strict, 'SELECTED_FULL_STEM': full, 'AUDIT_STEM': audit,
    'AUDIT_SHA': sha(audit_raw), 'FULL_RAW_BYTES': report['log_bytes'], 'FULL_RAW_SHA': report['log_sha256'],
    'TYPE_BYTES': len(checked), 'TYPE_CHARACTERS': len(checked.decode()), 'TYPE_LINE_FEEDS': checked.count(b'\n'),
    'TYPE_LOGICAL_LINES': len(checked.splitlines()), 'TYPE_FINAL_NEWLINE_JSON': json.dumps(checked.endswith(b'\n')),
    'TYPE_SHA': sha(checked), 'PUBLIC_TYPE_SHA': sha(checked), 'BODY_CHARACTERS': len(body.decode()), 'BODY_BYTES': len(body),
    'ACTUAL_AXIOMS_JSON': json.dumps(head['actual_axioms']), 'JOBS_JSON': json.dumps(jobs, sort_keys=True),
    'REJECTED_PUBLIC_STEMS_JSON': '[]', 'SOURCE_HISTORY_JSON': json.dumps(history, sort_keys=True),
    'CONTRACTS_JSON': json.dumps(contracts), 'FULL_READER_SHA': sha((here / 'full-preparation/check-full-public.py').read_bytes())}
names = ['verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py', 'archive-support.py',
    'seal-checkpoint.py', 'verify-seal.py', 'final-publication.py', 'update-documents.py', 'verify-proofs.py']
outputs, bindings = {}, {}
for filename in names:
    component = 'proof-verifier-preparation-v2' if filename == 'verify-proofs.py' else 'checkpoint-preparation'
    template_path = component + '/' + filename
    template = (here / template_path).read_text()
    result = template
    tokens = sorted(set(re.findall(r'__H20_(\w+)__', template)))
    for key in tokens:
        token = '__H20_' + key + '__'
        assert key in values, key
        if key.endswith('_JSON'):
            result, count = re.subn(r'([\x22\x27])' + re.escape(token) + r'\1', lambda _: repr(values[key]), result)
            assert count > 0 and token not in result
        else:
            result = result.replace(token, str(values[key]))
    assert not re.search(r'__H20_\w+__', result)
    parsed_template, parsed = ast.parse(template), ast.parse(result)
    assert sum(isinstance(x, ast.Assert) for x in ast.walk(parsed_template)) == sum(isinstance(x, ast.Assert) for x in ast.walk(parsed))
    outputs[filename] = result
    bindings[filename] = dict(template=template_path, template_sha256=sha(template.encode()),
        bound_sha256=sha(result.encode()), tokens=tokens)
assert all(not (here / path).exists() for path in [*outputs, 'source-history-gate.json',
    'frozen-modules.json', 'actual-bindings.json', 'actual-approved-contracts.json'])
(here / 'source-history-gate.json').write_text(json.dumps(history, indent=2) + '\n')
for filename, text in outputs.items():
    (here / filename).write_text(text)
(here / 'frozen-modules.json').write_text(json.dumps({name: source_sha}, indent=2) + '\n')
(here / 'actual-approved-contracts.json').write_text(json.dumps(contracts, indent=2) + '\n')
(here / 'actual-bindings.json').write_text(json.dumps(dict(status='BOUND_NOT_EXECUTED_REVIEW_PENDING',
    bindings=bindings, values=values, metrics=metrics, unchanged_assertion_counts=True,
    json_literals_bound_by_whole_quoted_replacement=True, contract_insertion_order_preserved=True,
    no_prepared_tool_executed=True), indent=2) + '\n')
print(json.dumps(dict(status='PASS', bound_tools=len(outputs), metrics=metrics,
    pending_independent_actual_binding_review=True)))
