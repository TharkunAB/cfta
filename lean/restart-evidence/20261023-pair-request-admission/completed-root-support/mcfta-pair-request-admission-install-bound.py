import ast
import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

package = Path('/tmp/mcfta-pair-request-admission-bound-actual')
audit = Path('/tmp/mcfta-pair-request-admission-bound-audit')
checked_package(package, 'a0ac19bdea290711c8c1a36310b6b5c36d95a0898b4dc9d8ebe31cff31ccae84',
    'e6a430b5f9f97acdf8208cd7263cbaf54924d54e9f91af1a276d6ff174c5edc6')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
selection = load(package / 'selected-scripts.json')
scripts = selection['scripts']
values = load(package / 'binding-values.json')
assert len(scripts) == 9 and len(values) == 31
seen = set()
lines = assertions = 0
for filename, pin in scripts.items():
    before = (package / 'predecessors' / filename).read_bytes()
    assert before == (HERE / 'checkpoint-preparation' / filename).read_bytes()
    data = before.decode()
    if filename == 'update-documents.py':
        for old, new in [
            ('Native Covered, generated-node composition, new-source Room, WordRanges,',
             'Native Covered for these comparisons, generated-node composition, new-source Room, WordRanges,'),
            ('No native Covered producer, generated-root composition, new-source Room,',
             'No native Covered producer for these comparisons, generated-root composition, new-source Room,')]:
            assert data.count(old) == 1
            data = data.replace(old, new)
        assert data == (package / 'update-documents.qualified-pending.py.txt').read_text()
    tokens = set(re.findall(r'__H25_[A-Z0-9_]+__', data))
    assert tokens <= set(values)
    seen.update(tokens)
    for token in sorted(tokens):
        value = values[token]
        if isinstance(value, (dict, list)):
            data, count = re.subn(r"(['\"])" + re.escape(token) + r'\1',
                lambda _: repr(json.dumps(value, ensure_ascii=False)), data)
            assert count > 0
        else:
            data = data.replace(token, str(value))
    selected = package / filename
    assert selected.read_bytes() == data.encode() and sha(selected) == pin['sha256']
    assert not re.search(r'__H25_[A-Z0-9_]+__', data)
    assert len(data.splitlines()) == pin['lines']
    count = sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(data)))
    assert count == pin['ast_assertions']
    lines += pin['lines']
    assertions += count
assert seen == set(values) and lines == 814 and assertions == 279
history = load(package / 'root-installation-proposals/source-history-gate.json')
assert history == values['__H25_SOURCE_HISTORY_JSON__']
assert history['status'] == 'ROOT_ACCEPTED'
assert len(history['variants']) == 2 and len(history['artifacts']) == 155 and len(history['patches']) == 1
assert history['rejected_public_types'] == []
proposals = load(package / 'root-installation-proposals.json')['files']
assert len(proposals) == 52
assert all(item['destination'].startswith('root-metadata-history/') for item in proposals[:47])
assert proposals[-1]['destination'] == 'source-history-gate.json'
by_destination = {item['destination']: item for item in proposals}
assert len(by_destination) == len(proposals)
for item in proposals:
    for key in ['source', 'destination']:
        relative = Path(item[key])
        assert not relative.is_absolute() and '..' not in relative.parts
    path = package / item['source']
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
    assert not (HERE / item['destination']).exists()
for item in history['variants'] + history['artifacts']:
    relative = Path(item['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    path = HERE / relative
    if not path.exists():
        path = package / by_destination[item['path']]['source']
    assert sha(path) == item['sha256']
    if 'lines' in item:
        assert len(path.read_bytes().splitlines()) == item['lines']
    else:
        assert path.stat().st_size == item['bytes']
assert git('rev-parse', 'HEAD').strip() == START
archive(package, 'bound-actual')
archive(audit, 'bound-audit')
for filename in scripts:
    assert not (HERE / filename).exists()
    (HERE / filename).write_bytes((package / filename).read_bytes())
for item in proposals:
    path = HERE / item['destination']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes((package / item['source']).read_bytes())
for item in history['variants'] + history['artifacts']:
    assert sha(HERE / item['path']) == item['sha256']
report = dict(status='ROOT_BOUND_TOOL_REVIEW_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    operational_scripts=9, operational_lines=lines, operational_assertions=assertions,
    composite_tools=12, composite_lines=1024, composite_assertions=332, bound_tokens=31,
    source_variants=2, source_artifacts=155, retained_source_patches=1, source_hard_stop=180,
    actual_jobs=3, failed_jobs=0, root_metadata_failures=4, root_metadata_successful_retries=4,
    root_read_scope='All1024 template program lines, exact31 structured metric/contract/scope bindings, source-history variants/patch and the two prose qualifications read. Bound814-line programs reconstruct exactly. All155 artifact hashes/bytes and52 proposed copies checked programmatically. No whole BODY manual read claim.',
    selected_scripts=scripts, independent_review_sha256=sha(audit / 'review.json'),
    prepared_scripts_executed=False, new_lean_lake_jobs=0)
save('root-bound-tools-review.json', report)
print(json.dumps({key:value for key,value in report.items() if key != 'selected_scripts'}))
