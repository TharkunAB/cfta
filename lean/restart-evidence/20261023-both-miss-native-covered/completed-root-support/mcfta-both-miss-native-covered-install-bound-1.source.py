import ast
import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

package = Path('/tmp/mcfta-both-miss-native-covered-bound-actual')
audit = Path('/tmp/mcfta-both-miss-native-covered-bound-audit')
erratum = Path('/tmp/mcfta-both-miss-native-covered-bound-audit-integrity-erratum')
checked_package(package, 'd48e57543f420e52e2ba07be6fafd7f172db632a45ed72ac19fc2861147de2f7',
    '59462a412de1af8045777f1fee5e0735fd0723ca1eb3046e2dce0b5b4703f9af')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
checked_package(erratum, 'bb06a7f8f37af582cabd841fd87d6042f06b6caeeaa8e8cf92bf004ac56fd434',
    '81ea0990bc285530d99f80d5650ad5c70c9cfe0a0373c1f0abfd4a29f50724ea')
assert sha(erratum / 'review.json') == '8094e93c8cbf2263b8653561b04e23c58b4c46423c05b151f69db28ccaccfdfb'
assert load(erratum / 'review.json')['status'] == 'CLEAR'
complete = load(erratum / 'complete-original-package-pins.json')['files']
assert set(complete) == {str(path.relative_to(audit)) for path in audit.rglob('*') if path.is_file()}
assert len(complete) == 48
for filename, pin in complete.items():
    assert (audit / filename).stat().st_size == pin['bytes'] and sha(audit / filename) == pin['sha256']
for filename in ['pins.json', 'FROZEN.json']:
    assert (audit / 'owner-inputs' / filename).read_bytes() == (package / filename).read_bytes()
scripts = load(package / 'selected-scripts.json')['scripts']
values = load(package / 'binding-values.json')['values']
assert len(scripts) == 9 and len(values) == 31
seen = set()
lines = assertions = 0
for filename, pin in scripts.items():
    before = (package / 'predecessors' / filename).read_bytes()
    predecessor = HERE / ('declaration-overlay' if filename == 'verify-proofs.py' else 'checkpoint-preparation') / filename
    assert before == predecessor.read_bytes()
    data = before.decode()
    tokens = set(re.findall(r'__H26_[A-Z0-9_]+__', data))
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
    assert not re.search(r'__H26_[A-Z0-9_]+__', data)
    assert len(data.splitlines()) == pin['lines']
    count = sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(data)))
    assert count == pin['ast_assertions']
    lines += pin['lines']
    assertions += count
assert seen == set(values) and lines == 837 and assertions == 292
assert values['__H26_SOURCE_SHA__'] == sha(ROOT / 'lean/MicroCFTA' / (NAME + '.lean'))
assert values['__H26_SOURCE_LINES__'] == 152 and values['__H26_SOURCE_HARD_STOP__'] == 180
scope = load(HERE / 'root-full-review-scope.json')
assert values['__H26_SCOPE_TRUE_KEYS_JSON__'] == scope['required_true']
assert values['__H26_SCOPE_FALSE_KEYS_JSON__'] == scope['required_false']
assert values['__H26_CONTRACT_SHA256__'] == sha(HERE / 'signature-plan/contracts.json')
history = load(package / 'root-installation-proposals/source-history-gate.json')
assert history == values['__H26_SOURCE_HISTORY_JSON__']
assert history['status'] == 'ROOT_ACCEPTED'
assert len(history['variants']) == 1 and len(history['artifacts']) == 278 and history['patches'] == []
assert history['rejected_public_types'] == []
proposals = load(package / 'root-installation-proposals.json')['files']
assert len(proposals) == 93
assert all(item['destination'].startswith('root-metadata-history/') for item in proposals[:88])
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
assert attempts['actual_attempts'] == attempts['successful_attempts'] == 12
assert attempts['failed_attempts'] == 0
assert all(item['exit_code'] == 0 for item in attempts['attempts'])
assert load(package / 'root-installation-proposals/frozen-modules.json') == {NAME: values['__H26_SOURCE_SHA__']}
assert git('rev-parse', 'HEAD').strip() == START
archive(package, 'bound-actual')
archive(audit, 'bound-audit')
archive(erratum, 'bound-audit-integrity-erratum')
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
    composite_tools=12, composite_lines=1047, composite_assertions=345, bound_tokens=31,
    source_variants=1, source_artifacts=278, retained_source_patches=0, source_hard_stop=180,
    actual_jobs=3, failed_jobs=0, root_metadata_attempts_at_binding_cut=12,
    root_metadata_failures_at_binding_cut=0,
    reviewer_two_nested_marker_pins_checked_directly=True,
    root_read_scope='All1047 template program lines, exact31 structured metric/contract/scope bindings and all152 ordinary source lines read. Bound837-line programs reconstruct exactly. Actual selected document writer and commit/checkpoint/publisher read in full. All278 artifact hashes/bytes and93 proposed copies checked programmatically. No whole BODY manual read claim.',
    selected_scripts=scripts, independent_review_sha256=sha(audit / 'review.json'),
    prepared_scripts_executed=False, new_lean_lake_jobs=0, whole_goal_complete=False)
save('root-bound-tools-review.json', report)
print(json.dumps({key:value for key,value in report.items() if key != 'selected_scripts'}))
