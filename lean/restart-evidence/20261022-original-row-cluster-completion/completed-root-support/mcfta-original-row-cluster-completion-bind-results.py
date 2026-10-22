import ast
import difflib
import hashlib
import json
import re
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
def sha(data):
    return hashlib.sha256(data).hexdigest()
def load(path):
    return json.loads((here / path).read_text())
strict = 'original-row-cluster-completion-strict-3'
full = 'original-row-cluster-completion-public-1'
audit = 'original-row-cluster-completion-audit-1'
assert load(audit + '.json')['exit_code'] == 0
audit_raw = (here / (audit + '.log')).read_bytes()
audit_text = audit_raw.decode()
build = re.search(r'Build completed successfully \((\d+) jobs\)\.', audit_text)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit_text)
assert build and dependencies and not re.search(r'\berror(?:\([^)]*\))?:', audit_text)
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
assert set(jobs) == {strict, full, audit, 'original-row-cluster-completion-strict-1', 'original-row-cluster-completion-strict-2'}
assert jobs[strict][0] == jobs[full][0] == jobs[audit][0] == 0
source_sha = jobs[strict][1]
selected = (here / (strict + '.source.lean')).read_bytes()
assert sha(selected) == source_sha == 'c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b'
assert len(selected.splitlines()) == 345
name = 'SourceCurrentOriginalRowClusterCompletion'
variant_paths = ['source-proposal/draft-1/' + name + '.lean',
    'original-row-cluster-completion-strict-1.source.lean',
    'original-row-cluster-completion-strict-2.source.lean', strict + '.source.lean']
variants = [dict(path=path, sha256=sha((here / path).read_bytes()), lines=len((here / path).read_bytes().splitlines())) for path in variant_paths]
patch_specs = [('source-proposal/preflight.patch', 0, 1), ('source-repair-v2/repair.patch', 1, 2), ('source-repair-v3/repair.patch', 2, 3)]
patches = []
for path, before, after in patch_specs:
    data = (here / path).read_text()
    lines = data.splitlines()
    labels = [lines[0][4:], lines[1][4:]]
    assert lines[0].startswith('--- ') and lines[1].startswith('+++ ')
    expected = ''.join(difflib.unified_diff((here / variant_paths[before]).read_text().splitlines(True),
        (here / variant_paths[after]).read_text().splitlines(True), fromfile=labels[0], tofile=labels[1]))
    assert data == expected
    patches.append(dict(path=path, sha256=sha(data.encode()), before=variant_paths[before], after=variant_paths[after], fromfile=labels[0], tofile=labels[1]))
artifact_paths = {path for path, _, _ in patch_specs} | {'source-proposal/source-addition.patch',
    'signature-plan/context.lean.txt', 'source-repair-v2/context.lean.txt'}
for stem in jobs:
    artifact_paths.update(stem + suffix for suffix in ['.json', '.log', '.limits.json', '.usage.json'])
artifact_paths.add(full + '.source.lean')
artifacts = [dict(path=path, sha256=sha((here / path).read_bytes()), bytes=len((here / path).read_bytes())) for path in sorted(artifact_paths)]
history = dict(status='ROOT_ACCEPTED', selected_source_sha256=source_sha, variants=variants,
    artifacts=artifacts, patches=patches, rejected_public_types=[])
assert not (here / 'source-history-gate.json').exists()
report = load('public-readback/original-row-cluster-completion-full-readback.json')
head = report['heads'][0]
checked = (here / 'public-readback/original-row-cluster-completion-cluster_complete-public-type.txt').read_bytes()
body = (here / 'public-readback/original-row-cluster-completion-cluster_complete-body.txt').read_bytes()
metrics = dict(ACTUAL_JOBS=len(jobs), SOURCE_JOBS=sum(bool(row[1]) for row in jobs.values()),
    AUDIT_JOBS=sum(not row[1] for row in jobs.values()), FAILED_JOBS=sum(row[0] != 0 for row in jobs.values()),
    WARNED_SOURCE_EXIT_ZERO_JOBS=sum(row[0] == 0 and bool(row[1]) and bool(row[4]) for row in jobs.values()),
    REJECTED_PUBLIC_TYPE_JOBS=0, AUDIT_BUILD_JOBS=int(build.group(1)), AUDIT_DEPENDENCIES=int(dependencies.group(1)))
values = {**metrics, 'SELECTED_SOURCE_SHA': source_sha, 'SOURCE_SHA': source_sha, 'SOURCE_LINES': len(selected.splitlines()),
    'SELECTED_STRICT_STEM': strict, 'SELECTED_FULL_STEM': full, 'AUDIT_STEM': audit,
    'AUDIT_LOG_SHA': sha(audit_raw), 'BACKUP_BRANCH': 'codex/backup-original-row-cluster-completion-20261022-0636',
    'FULL_RAW_BYTES': report['log_bytes'], 'FULL_LOG_SHA': report['log_sha256'],
    'TYPE_BYTES': len(checked), 'TYPE_CHARACTERS': len(checked.decode()), 'TYPE_LINE_FEEDS': checked.count(b'\n'),
    'TYPE_LOGICAL_LINES': len(checked.splitlines()), 'TYPE_FINAL_NEWLINE_JSON': json.dumps(checked.endswith(b'\n')),
    'TYPE_SHA': sha(checked), 'CLUSTER_COMPLETE_TYPE_SHA': sha(checked), 'BODY_CHARACTERS': len(body.decode()), 'BODY_BYTES': len(body),
    'ACTUAL_AXIOMS_JSON': json.dumps(head['actual_axioms']), 'CLUSTER_COMPLETE_ACTUAL_AXIOMS_JSON': json.dumps(head['actual_axioms']),
    'JOBS_JSON': json.dumps(jobs, sort_keys=True), 'REJECTED_PUBLIC_STEMS_JSON': '[]', 'SOURCE_HISTORY_JSON': json.dumps(history, sort_keys=True),
    'FULL_READER_SHA': sha((here / 'full-preparation/check-full-public.py').read_bytes())}
names = ['verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py', 'archive-support.py',
    'seal-checkpoint.py', 'verify-seal.py', 'final-publication.py', 'update-documents.py', 'verify-proofs.py']
outputs = {}
bindings = {}
for filename in names:
    component = 'proof-verifier-preparation-v2' if filename == 'verify-proofs.py' else 'checkpoint-preparation'
    template_path = component + '/' + filename
    template = (here / template_path).read_text()
    result = template
    tokens = sorted(set(re.findall(r'__H17_(\w+)__', template)))
    for key in tokens:
        token = '__H17_' + key + '__'
        assert key in values, key
        if key.endswith('_JSON'):
            result, count = re.subn(r'([\x22\x27])' + re.escape(token) + r'\1', lambda _: repr(values[key]), result)
            assert count > 0 and token not in result
        else:
            result = result.replace(token, str(values[key]))
    assert not re.search(r'__H17_\w+__', result)
    parsed_template, parsed = ast.parse(template), ast.parse(result)
    assert sum(isinstance(x, ast.Assert) for x in ast.walk(parsed_template)) == sum(isinstance(x, ast.Assert) for x in ast.walk(parsed))
    assert not (here / filename).exists()
    outputs[filename] = result
    bindings[filename] = dict(template=template_path, template_sha256=sha(template.encode()), bound_sha256=sha(result.encode()), tokens=tokens)
assert not (here / 'frozen-modules.json').exists()
(here / 'source-history-gate.json').write_text(json.dumps(history, indent=2) + '\n')
for filename, source in outputs.items():
    (here / filename).write_text(source)
(here / 'frozen-modules.json').write_text(json.dumps({name: source_sha}, indent=2) + '\n')
(here / 'actual-bindings.json').write_text(json.dumps(dict(status='BOUND_NOT_EXECUTED_REVIEW_PENDING',
    bindings=bindings, values=values, metrics=metrics, unchanged_assertion_counts=True,
    json_literals_bound_by_whole_quoted_replacement=True, no_prepared_tool_executed=True), indent=2) + '\n')
print(json.dumps(dict(status='PASS', bound_tools=len(outputs), metrics=metrics, pending_independent_actual_binding_review=True)))
