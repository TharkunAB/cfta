import ast
import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

package = Path('/tmp/mcfta-completed-hit-readback-evidence-binding')
audit = Path('/tmp/mcfta-completed-hit-readback-evidence-binding-audit')
def complete_package(path, pins_hash, freeze_hash):
    entries = checked_package(path, pins_hash, freeze_hash)
    actual = {str(item.relative_to(path)) for item in path.rglob('*') if item.is_file()}
    assert actual == {item['path'] for item in entries} | {'pins.json', 'FROZEN.json'}
    return entries
assert len(complete_package(package,
    'f73e5227e45105388c89c771efd4f20060c54149fbfbbd7eab2a42199c2797bb',
    '6cbeccb63dadaba0c71986893c35e5c2684f86b595c6d125eabe0eebfcf1fa85')) == 676
complete_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'SOURCE_ONLY_CLEAR'
scripts = load(package / 'selected-scripts.json')['scripts']
values = load(package / 'binding-values.json')['values']
assert len(scripts) == 9 and len(values) == 32
seen = set()
lines = assertions = 0
for filename, pin in scripts.items():
    before = (package / 'predecessors' / filename).read_bytes()
    predecessor = HERE / ('declaration-overlay' if filename == 'verify-proofs.py' else 'checkpoint-preparation') / filename
    assert before == predecessor.read_bytes()
    data = before.decode()
    tokens = set(re.findall(r'__H27_[A-Z0-9_]+__', data))
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
    assert not re.search(r'__H27_[A-Z0-9_]+__', data)
    assert len(data.splitlines()) == pin['lines']
    count = sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(data)))
    assert count == pin['AST_assertions']
    lines += pin['lines']
    assertions += count
assert seen == set(values) and lines == 865 and assertions == 315
assert values['__H27_SOURCE_SHA__'] == sha(ROOT / 'lean/MicroCFTA' / (NAME + '.lean'))
assert values['__H27_SOURCE_LINES__'] == 147 and values['__H27_SOURCE_HARD_STOP__'] == 180
assert values['__H27_PRIVATE_NAMES_JSON__'] == ['yielded_done', 'ret_checked']
for spec in values['__H27_HEAD_SPECS_JSON__']:
    assert json.loads(spec[-1]) == ['Classical.choice', 'Quot.sound', 'propext']
scope = load(HERE / 'root-full-review-scope.json')
assert values['__H27_SCOPE_TRUE_KEYS_JSON__'] == scope['required_true']
assert values['__H27_SCOPE_FALSE_KEYS_JSON__'] == scope['required_false']
assert values['__H27_CONTRACT_SHA256__'] == sha(HERE / 'signature-plan/contracts.json')
history = load(package / 'root-installation-proposals/source-history-gate.json')
assert history == values['__H27_SOURCE_HISTORY_JSON__']
assert history == load(package / 'source-history-proposal.json')['proposed_source_history']
assert history['status'] == 'ROOT_ACCEPTED'
assert len(history['variants']) == 2 and len(history['artifacts']) == 524 and len(history['patches']) == 1
assert history['rejected_public_types'] == []
proposals = load(package / 'root-installation-proposals.json')['files']
assert len(proposals) == 86
assert all(item['destination'].startswith('root-metadata-history/') for item in proposals[:-5])
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
attempts = load(package / 'metadata-attempts.json')
assert attempts['actual_attempts'] == attempts['successful_attempts'] == 11
assert attempts['failed_attempts'] == 0
assert all(item['exit_code'] == 0 for item in attempts['attempts'])
assert load(package / 'root-installation-proposals/frozen-modules.json') == {NAME: values['__H27_SOURCE_SHA__']}
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
    composite_tools=12, composite_lines=1075, composite_assertions=368, bound_tokens=32,
    source_variants=2, source_artifacts=524, retained_source_patches=1, source_hard_stop=180,
    actual_jobs=3, failed_jobs=0, root_metadata_attempts_at_binding_cut=11,
    root_metadata_failures_at_binding_cut=0, package_file_sets_and_nested_marker_pins_checked=True,
    root_read_scope='All1075 template program lines, exact32 structured metric/contract/scope bindings and all147 ordinary source lines read. Bound865-line programs reconstruct exactly. Actual document writer and commit/checkpoint/publisher read in full. All524 artifact hashes/bytes and86 proposed copies checked programmatically. No whole BODY manual read claim.',
    selected_scripts=scripts, independent_review_sha256=sha(audit / 'review.json'),
    prepared_scripts_executed=False, new_lean_lake_jobs=0, whole_goal_complete=False)
save('root-bound-tools-review.json', report)
print(json.dumps({key:value for key,value in report.items() if key != 'selected_scripts'}))
