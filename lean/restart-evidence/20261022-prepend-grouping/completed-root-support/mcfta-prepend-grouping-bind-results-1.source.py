import ast
import difflib
import hashlib
import json
import re
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-prepend-grouping')
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda name: json.loads((here / name).read_text())
strict, full, audit = 'prepend-grouping-strict-3', 'prepend-grouping-public-1', 'prepend-grouping-audit-1'
assert load(audit + '.json')['exit_code'] == 0
assert 'CLEAR' in (here / 'proof-verifier-audit-v3/review.md').read_text()
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
    counts = [len(re.findall(r'^.+?:\d+:\d+: ' + kind + r'(?:\([^)]*\))?:', raw.decode(), re.M)) for kind in ['error','warning']]
    jobs[path.stem] = [item['exit_code'], item.get('sha256'), sha(raw), *counts]
assert {strict, full, audit} <= set(jobs)
selected = (here / (strict + '.source.lean')).read_bytes()
source_sha = sha(selected)
assert source_sha == '3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba'
assert (here / (strict + '.log')).read_bytes() == b''
name = 'SourceCurrentPrependGrouping'
variants = []
reasons = [
    ('source-proposal', 'Uncompiled proposal retained after source review found lookup normalization issue.'),
    ('source-proposal-v2', 'One lookup-case repair; actual strict1 failed with four errors.'),
    ('source-proposal-v3', 'Four error repairs; actual strict2 failed at empty-table function equality.'),
    ('source-proposal-v4', 'Repair empty-table function equality; strict3 clean and sole FULL1 passed.')]
for component, reason in reasons:
    path = component + '/' + name + '.lean'
    data = (here / path).read_bytes()
    variants.append(dict(path=path,sha256=sha(data),lines=len(data.splitlines()),reason=reason))
artifact_paths = {'root-peaks.txt', 'root-full-review.json', 'root-reader-v2-review.json'}
for stem, row in jobs.items():
    artifact_paths.update(stem + suffix for suffix in ['.json','.log','.limits.json','.usage.json'])
    if row[1]:
        path = stem + '.source.lean'
        if 'public' in stem:
            artifact_paths.add(path)
        else:
            data = (here / path).read_bytes()
            assert any(pin['sha256'] == sha(data) for pin in variants)
            variants.append(dict(path=path,sha256=sha(data),lines=len(data.splitlines()),reason='Exact actual ordinary-check input: ' + stem))
patches = []
for index, patch_name, reason in [
    (1,'precheck-lookup-normalization.patch','Use the normalized rowKey lookup case.'),
    (2,'four-error-repair.patch','Repair four actual strict1 elaboration errors.'),
    (3,'empty-table-function-repair.patch','Repair the remaining actual strict2 empty-table equality.')]:
    path = reasons[index][0] + '/' + patch_name
    before, after = [reasons[i][0] + '/' + name + '.lean' for i in [index-1,index]]
    fromfile, tofile = 'v' + str(index) + '/' + name + '.lean', 'v' + str(index+1) + '/' + name + '.lean'
    expected = ''.join(difflib.unified_diff((here / before).read_text().splitlines(True),(here / after).read_text().splitlines(True),fromfile=fromfile,tofile=tofile))
    assert (here / path).read_text() == expected
    artifact_paths.add(path)
    patches.append(dict(reason=reason,before=before,after=after,path=path,sha256=sha(expected.encode()),fromfile=fromfile,tofile=tofile))
for component in ['full-preparation-v2/actual-failed-reader-1', 'full-public-audit/actual-reader-metadata']:
    artifact_paths.update(str(path.relative_to(here)) for path in (here / component).rglob('*') if path.is_file())
template = (here / 'proof-verifier-preparation-v3/verify-proofs.py').read_text()
contract_node = next(statement.value for statement in ast.parse(template).body if isinstance(statement,ast.Assign) and any(isinstance(target,ast.Name) and target.id == 'expected_contracts' for target in statement.targets))
contracts = ast.literal_eval(contract_node)
artifact_paths.update(pin['path'] for pin in contracts.values())
history = dict(status='ROOT_ACCEPTED', selected_source_sha256=source_sha, variants=variants,
    artifacts=[dict(path=path,sha256=sha((here / path).read_bytes()),bytes=(here / path).stat().st_size) for path in sorted(artifact_paths)],
    patches=patches,rejected_public_types=[])
report = load('public-readback/prepend-grouping-full-readback.json')
assert report['source_sha256'] == source_sha and report['log_sha256'] == jobs[full][2]
head_metrics, head_specs = {}, []
for head in report['heads']:
    short = head['head'].rsplit('.',1)[1]
    paths = {suffix:'public-readback/prepend-grouping-' + short + '-' + suffix + '.txt' for suffix in ['public-type','printed-public-type','body']}
    checked, printed, body = [(here / paths[suffix]).read_bytes() for suffix in ['public-type','printed-public-type','body']]
    head_metrics[short] = dict(type_bytes=len(checked),type_characters=len(checked.decode()),type_logical_lines=len(checked.splitlines()),type_line_feeds=checked.count(b'\n'),type_final_newline=checked.endswith(b'\n'),type_sha256=sha(checked),body_bytes=len(body),body_characters=len(body.decode()),body_sha256=sha(body),actual_axioms=head['actual_axioms'],printed_type_bytes=len(printed),printed_type_sha256=sha(printed),raw_type_byte_identity=checked == printed)
    head_specs.append([short,sha(checked),sha(printed),head['canonical_type_sha256'],checked == printed,paths['public-type'],paths['printed-public-type'],json.dumps(head['actual_axioms'])])
metrics = dict(ACTUAL_JOBS=len(jobs),SOURCE_JOBS=sum(bool(row[1]) for row in jobs.values()),AUDIT_JOBS=sum(not row[1] for row in jobs.values()),FAILED_JOBS=sum(row[0] != 0 for row in jobs.values()),WARNED_SOURCE_EXIT_ZERO_JOBS=sum(row[0] == 0 and bool(row[1]) and bool(row[4]) for row in jobs.values()),REJECTED_PUBLIC_TYPE_JOBS=0,AUDIT_BUILD_JOBS=int(build.group(1)),AUDIT_DEPENDENCIES=int(dependencies.group(1)))
values = {**metrics,'SELECTED_SOURCE_SHA':source_sha,'SOURCE_SHA':source_sha,'SOURCE_LINES':len(selected.splitlines()),'SELECTED_STRICT_STEM':strict,'SELECTED_FULL_STEM':full,'AUDIT_STEM':audit,'AUDIT_SHA':sha(audit_raw),'FULL_RAW_BYTES':report['log_bytes'],'FULL_RAW_SHA':report['log_sha256'],'FULL_READER_SHA':sha((here / 'check-full-public-v2.py').read_bytes()),'JOBS_JSON':json.dumps(jobs),'REJECTED_PUBLIC_STEMS_JSON':'[]','SOURCE_HISTORY_JSON':json.dumps(history),'CONTRACTS_JSON':json.dumps(contracts),'HEAD_METRICS_JSON':json.dumps(head_metrics),'HEAD_SPECS_JSON':json.dumps(head_specs)}
outputs, bindings = {}, {}
names = ['verify-preservation.py','verify-checkpoint.py','commit-proofs.py','archive-support.py','seal-checkpoint.py','verify-seal.py','final-publication.py','update-documents.py','verify-proofs.py']
for filename in names:
    component = 'proof-verifier-preparation-v3' if filename == 'verify-proofs.py' else 'checkpoint-preparation-v2'
    path = component + '/' + filename
    original = (here / path).read_text()
    bound = original
    tokens = sorted(set(re.findall(r'__H21_(\w+)__', original)))
    for key in tokens:
        token = '__H21_' + key + '__'
        assert key in values
        if key.endswith('_JSON'):
            bound, count = re.subn(r'([\x22\x27])' + re.escape(token) + r'\1',lambda _:repr(values[key]),bound)
            assert count > 0 and token not in bound
        else:
            bound = bound.replace(token,str(values[key]))
    assert not re.search(r'__H21_\w+__',bound)
    assert sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(original))) == sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(bound)))
    outputs[filename] = bound
    bindings[filename] = dict(template=path,template_sha256=sha(original.encode()),bound_sha256=sha(bound.encode()),tokens=tokens)
assert all(not (here / path).exists() for path in [*outputs,'source-history-gate.json','actual-bindings.json','actual-approved-contracts.json'])
(here / 'source-history-gate.json').write_text(json.dumps(history,indent=2) + '\n')
(here / 'actual-approved-contracts.json').write_text(json.dumps(contracts,indent=2) + '\n')
for filename, text in outputs.items():
    (here / filename).write_text(text)
(here / 'actual-bindings.json').write_text(json.dumps(dict(status='BOUND_NOT_EXECUTED_REVIEW_PENDING',bindings=bindings,values=values,metrics=metrics,unchanged_assertion_counts=True,json_literals_bound_by_whole_quoted_replacement=True,contract_insertion_order_preserved=True,no_prepared_tool_executed=True),indent=2) + '\n')
print(json.dumps(dict(status='PASS',bound_tools=len(outputs),metrics=metrics,pending_independent_actual_binding_review=True)))
