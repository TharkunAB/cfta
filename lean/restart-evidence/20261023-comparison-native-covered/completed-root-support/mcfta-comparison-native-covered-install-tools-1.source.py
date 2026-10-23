import ast
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

# Each package remains frozen. Arguments supply separately reviewed identities.
specs = [
    ('proof-verifier-plan', 'proof-verifier-plan'),
    ('proof-verifier-audit', 'proof-verifier-audit'),
    ('proof-verifier-overlay', 'proof-verifier-overlay'),
    ('proof-verifier-overlay-audit', 'proof-verifier-overlay-audit'),
    ('bound-tools', 'bound-tools'),
    ('bound-tools-audit', 'bound-tools-audit'),
]
assert len(sys.argv) == 13
for index, (suffix, destination) in enumerate(specs):
    path = Path('/tmp/mcfta-comparison-native-covered-' + suffix)
    checked_package(path, sys.argv[index * 2 + 1], sys.argv[index * 2 + 2])
    if suffix == 'proof-verifier-overlay-audit':
        assert load(path / 'review.json')['status'] == 'SOURCE_ONLY_THREE_ADAPTER_OVERLAY_CLEAR'
    if suffix == 'bound-tools-audit':
        assert load(path / 'review.json')['status'] == 'CLEAR'
    archive(path, destination)
bound = Path('/tmp/mcfta-comparison-native-covered-bound-tools')
bindings = load(bound / 'bindings.json')
scalars, values = bindings['scalars'], bindings['json_values']
assert scalars['ACTUAL_JOBS'] == 3 and scalars['SOURCE_JOBS'] == 2 and scalars['AUDIT_JOBS'] == 1
assert scalars['FAILED_JOBS'] == scalars['WARNED_SOURCE_EXIT_ZERO_JOBS'] == scalars['REJECTED_PUBLIC_TYPE_JOBS'] == 0
assert values['JOBS_JSON'] == load(HERE / 'actual-result-data.json')['jobs']
assert values['ROOT_METADATA_JOBS_JSON'] == load(HERE / 'actual-result-data.json')['metadata_jobs']
assert values['SOURCE_HISTORY_JSON'] == load(HERE / 'source-history-gate.json')
assert sum(code != 0 for code in values['ROOT_METADATA_JOBS_JSON'].values()) == 3
assert values['HEAD_SPECS_JSON'][0][-1] == json.dumps(['Classical.choice', 'Quot.sound', 'propext'])
ledger = load(bound / 'selected-scripts.json')
assert len(ledger) == 9
for name, pin in ledger.items():
    target = HERE / name
    source = bound / 'selected' / name
    assert not target.exists() and sha(source) == pin['selected_sha256']
    text = source.read_text()
    reconstructed = (bound / 'basis' / name).read_text()
    for token in pin['tokens']:
        key = token[6:-2]
        if key in values:
            reconstructed = re.sub(r'([\x22\x27])' + re.escape(token) + r'\1',
                lambda match: repr(json.dumps(values[key], ensure_ascii=False)), reconstructed)
        else:
            reconstructed = reconstructed.replace(token, str(scalars[key]))
    assert reconstructed == text
    assert not re.search(r'__H28_[A-Z0-9_]+__', text)
    ast.parse(text)
    target.write_bytes(source.read_bytes())
save('root-bound-tools-review.json', dict(status='ROOT_ACCEPTED', programs=9,
    root_complete_pending_sources_and_overlay_read=True,
    root_all_scalar_JSON_text_bindings_reviewed=True,
    root_source_history_hashes_programmatically_checked=True,
    root_nested_HEAD_SPECS_axioms_JSON_checked=True,
    independent_binding_review_sha256=sha(Path('/tmp/mcfta-comparison-native-covered-bound-tools-audit/review.json')),
    data_only_binding_inverse_verified=True, prepared_programs_executed_before_gate=False,
    next_action='Standalone normal/live verify-proofs from cwd=/, before documents.', whole_goal_complete=False))
print(json.dumps(dict(status='PASS', installed_programs=9, standalone_before_documents_required=True)))
