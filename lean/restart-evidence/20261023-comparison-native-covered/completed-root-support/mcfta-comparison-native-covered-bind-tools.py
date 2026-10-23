import ast
import difflib
import re
import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

# This preparation writes only a new temporary package.
owner = Path('/tmp/mcfta-comparison-native-covered-bound-tools')
assert not owner.exists()
owner.mkdir()
results = load(HERE / 'actual-result-data.json')
readback = load(HERE / 'public-readback/comparison-native-covered-full-readback.json')
head, = readback['heads']
short = head['head'].rsplit('.', 1)[1]
type_path = 'public-readback/comparison-native-covered-' + short + '-public-type.txt'
printed_path = 'public-readback/comparison-native-covered-' + short + '-printed-public-type.txt'
body_path = 'public-readback/comparison-native-covered-' + short + '-body.txt'
type_data = (HERE / type_path).read_bytes()
body_data = (HERE / body_path).read_bytes()
metrics = dict(type_bytes=len(type_data), type_characters=len(type_data.decode()),
    type_logical_lines=len(type_data.splitlines()), type_line_feeds=type_data.count(b'\n'),
    type_final_newline=type_data.endswith(b'\n'), type_sha256=sha(HERE / type_path),
    body_bytes=len(body_data), body_characters=len(body_data.decode()), body_sha256=sha(HERE / body_path),
    actual_axioms=head['actual_axioms'], printed_type_bytes=(HERE / printed_path).stat().st_size,
    printed_type_sha256=sha(HERE / printed_path), raw_type_byte_identity=type_data == (HERE / printed_path).read_bytes())
scalars = dict(SELECTED_SOURCE_SHA=readback['source_sha256'], SOURCE_SHA=readback['source_sha256'],
    SOURCE_LINES=readback['source_lines'], SOURCE_HARD_STOP=230,
    SELECTED_STRICT_STEM='comparison-native-covered-strict-1', SELECTED_FULL_STEM='comparison-native-covered-public-1',
    AUDIT_STEM='comparison-native-covered-audit-1', ACTUAL_JOBS=len(results['jobs']), SOURCE_JOBS=2,
    AUDIT_JOBS=1, FAILED_JOBS=0, WARNED_SOURCE_EXIT_ZERO_JOBS=0, REJECTED_PUBLIC_TYPE_JOBS=0,
    AUDIT_BUILD_JOBS=results['audit_build_jobs'], AUDIT_DEPENDENCIES=results['audit_dependencies'],
    AUDIT_SHA=results['audit_log_sha256'], FULL_RAW_SHA=readback['log_sha256'], FULL_RAW_BYTES=readback['log_bytes'],
    FULL_READER_SHA=sha(HERE / 'check-full-public.py'))
contracts = {}
layout = load(HERE / 'signature-plan/insertion-map.json')
for item in layout['compiled_fragments']:
    contracts[item['file']] = dict(path='signature-plan/' + item['file'], lines=item['lines'], sha256=item['sha256'])
json_values = dict(JOBS_JSON=results['jobs'], REJECTED_PUBLIC_STEMS_JSON=[],
    ROOT_METADATA_JOBS_JSON=results['metadata_jobs'], SOURCE_HISTORY_JSON=load(HERE / 'source-history-gate.json'),
    CONTRACTS_JSON=contracts, HEAD_METRICS_JSON={short:metrics},
    HEAD_SPECS_JSON=[[short, head['checked_type_sha256'], head['printed_type_sha256'], head['canonical_type_sha256'],
        head['check_print_type_byte_identity'], type_path, printed_path, json.dumps(head['actual_axioms'])]],
    PUBLIC_HEAD_NAMES_JSON=[short], SCOPE_TRUE_KEYS_JSON=['source_complete_root_and_independent_reviews'],
    SCOPE_FALSE_KEYS_JSON=['whole_goal_complete'])
texts = load(Path('/tmp/mcfta-comparison-native-covered-document-scope.json'))
for token, value in texts.items():
    assert token.startswith('__H28_') and token.endswith('__') and token.endswith('_JSON__')
    json_values[token[6:-2]] = value
bindings = {'__H28_' + key + '__':value for key, value in {**scalars, **json_values}.items()}
json_tokens = {'__H28_' + key + '__' for key in json_values}
selected = {item['path']: item for item in load(HERE / 'pending-tools/selected-scripts.json')['scripts']}
assert len(selected) == 8
# The reviewed schema overlay supplies only the ninth program.
overlay = Path('/tmp/mcfta-comparison-native-covered-proof-verifier-overlay')
assert (overlay / 'verify-proofs.py').is_file()
bases = {name: HERE / 'pending-tools/selected' / name for name in selected}
bases['verify-proofs.py'] = overlay / 'verify-proofs.py'
ledger = {}
(owner / 'selected').mkdir()
(owner / 'basis').mkdir()
(owner / 'diffs').mkdir()
used = set()
for name, path in bases.items():
    before = path.read_text()
    tokens = set(re.findall(r'__H28_[A-Z0-9_]+__', before))
    assert tokens <= set(bindings), (name, tokens - set(bindings))
    after = before
    for token in sorted(tokens):
        value = bindings[token]
        if token in json_tokens:
            pattern = r'([\x22\x27])' + re.escape(token) + r'\1'
            after, count = re.subn(pattern, lambda match: repr(json.dumps(value, ensure_ascii=False)), after)
            assert count == before.count(token)
        else:
            assert isinstance(value, int) or re.fullmatch(r'[a-z0-9-]+', value), token
            after = after.replace(token, str(value))
    assert not re.search(r'__H28_[A-Z0-9_]+__', after)
    tree = ast.parse(after)
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id == 'json' and node.func.attr == 'loads' and node.args and isinstance(node.args[0], ast.Constant):
            json.loads(node.args[0].value)
    (owner / 'selected' / name).write_text(after)
    (owner / 'basis' / name).write_text(before)
    (owner / 'diffs' / (name + '.patch')).write_text(''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile='basis/' + name, tofile='selected/' + name)))
    ledger[name] = dict(basis_sha256=sha(path), selected_sha256=sha(owner / 'selected' / name), lines=len(after.splitlines()), tokens=sorted(tokens))
    used |= tokens
assert len(ledger) == 9
(owner / 'bindings.json').write_text(json.dumps(dict(scalars=scalars, json_values=json_values), indent=2, ensure_ascii=False) + '\n')
(owner / 'selected-scripts.json').write_text(json.dumps(ledger, indent=2) + '\n')
(owner / 'review-boundary.json').write_text(json.dumps(dict(status='SOURCE_ONLY_PENDING_ROOT_AND_INDEPENDENT_BINDING_REVIEW',
    programs=9, tokens=sorted(used), actual_results_sha256=sha(HERE / 'actual-result-data.json'),
    source_history_sha256=sha(HERE / 'source-history-gate.json'),
    whole_goal_complete=False, prepared_programs_executed=False), indent=2) + '\n')
pins = [dict(path=str(path.relative_to(owner)), bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.rglob('*')) if path.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_SOURCE_ONLY', pins_sha256=sha(owner / 'pins.json')), indent=2) + '\n')
print(json.dumps(dict(status='PREPARED_SOURCE_ONLY', programs=9, pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'))))
