import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

package = Path('/tmp/mcfta-comparison-native-covered-signature-plan')
checked_package(package,
    'cf2bd12464549d63d7af0aa444ec10841de2e9317dddf2ece2d1d1972c5fc122',
    '48d97875f1b5ff6d7973b4da66342125a88d79be7437c26bf7dee9f8e8842bf1')
audit = Path('/tmp/mcfta-comparison-native-covered-signature-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == sys.argv[4]
assert sys.argv[4] in ('CLEAR', 'SOURCE_ONLY_CLEAR', 'SOURCE_ONLY_EXACT_DECLARATIONS_CLEAR')
schema = load(package / 'declaration-schema.json')
assert schema['public_heads'] == ['MicroCFTA.' + NAME + '.original_rows_complete']
assert schema['private_helpers'] == schema['global_definitions'] == [] and schema['induction'] is None
assert len(schema['local_have_names']) == 16 and len(schema['local_let_names']) == 3
assert schema['source_hard_stop'] == 230 and schema['required_body_prologue'] == ['  classical']
contracts = load(package / 'contracts.json')
assert len(contracts) == 25 and sha(package / 'contracts.json') == 'ef962dae21c171cc1e2a02a80ecb73ac8af5e1cfc2c7129b8e55c3947aeacbc4'
fragments = load(package / 'insertion-map.json')['compiled_fragments']
assert [item['file'] for item in fragments] == schema['compiled_contract_order'] == list(contracts)
for fragment in fragments:
    path = package / fragment['file']
    assert sha(path) == fragment['sha256'] == contracts[fragment['file']]
    assert len(path.read_bytes().splitlines()) == fragment['lines']
assert sum(item['lines'] for item in fragments) == 131
budget = load(package / 'budget.json')
assert budget['whole_source_estimate'] == [212, 226] and budget['proposed_hard_stop'] == 230
assert budget['private_helpers'] == 0 and not budget['induction']
source_index = load(package / 'source-index.json')
cut_count = 0
for pin in source_index['sources']:
    path = Path(pin['path'])
    assert path.is_relative_to(ROOT) and path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
    assert Path(pin['full_snapshot_reference']).read_bytes() == path.read_bytes()
    lines = path.read_bytes().splitlines(keepends=True)
    for cut in pin['cuts']:
        literal = b''.join(lines[cut['start'] - 1:cut['end']])
        snapshot = package / cut['snapshot']
        assert snapshot.read_bytes() == literal and len(literal) == cut['bytes'] and sha(snapshot) == cut['sha256']
        cut_count += 1
assert len(source_index['sources']) == 29 and cut_count == 35
routes = load(package / 'public-import-routes.json')
for route in routes['selected_public_source_routes']:
    if route['role'] != 'public_imported_API':
        continue
    chain = route['import_path']
    assert chain[0] in routes['context_imports'] and chain[-1] == route['module']
    for parent, child in zip(chain, chain[1:]):
        code = (ROOT / 'lean' / (parent.replace('.', '/') + '.lean')).read_text()
        assert 'import ' + child in code.splitlines()
    assert sha(ROOT / 'lean' / (route['module'].replace('.', '/') + '.lean')) == route['source_sha256']
old = (ROOT / 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparisonDomains.lean').read_text()
old = old[old.index('theorem original_rows_complete'):].split(' := by\n', 1)[0]
old_parameters = '    (inputModel : InputMeaning (view source (guardHolds formulas solver)))\n    (inputRanked : RankedInput (view source (guardHolds formulas solver)) inputModel.valid)'
assert old.count(old_parameters) == 1
derived = old.replace(old_parameters, '    (inputs : FiniteInput (view source (guardHolds formulas solver)))')
derived = re.sub(r'\binputModel\b', '(finiteInputMeaning (view source (guardHolds formulas solver)) inputs)', derived)
derived = re.sub(r'\binputRanked\b', '(finiteRankedInput (view source (guardHolds formulas solver)) inputs)', derived)
anchor = '    (leftClosed : leftParent.free = []) (rightClosed : rightParent.free = [])'
derived = derived.replace(anchor, anchor + '\n    (leftAdmitted : inputs.valid (inputOf leftParent))\n    (rightAdmitted : inputs.valid (inputOf rightParent))')
anchor = '    (semantic : SemanticReady before.checked.native.machine.heap)'
derived = derived.replace(anchor, anchor + '\n    (covered : Covered inputs before.checked.native)')
derived += ' ∧\n      Covered inputs after.checked.native'
header = (package / 'public-header.lean.txt').read_text()
header = header[header.index('theorem original_rows_complete'):]
normalize = lambda value: re.sub(r'\s+', ' ', value).strip()
assert normalize(derived) == normalize(header)
archive(package, 'signature-plan')
archive(audit, 'signature-audit')
save('root-declaration-review.json', dict(status='ROOT_ACCEPTED',
    observed_at=datetime.datetime.now().astimezone().isoformat(), module=NAME,
    public_heads=schema['public_heads'], whole_source_cap=230, source_estimate=[212, 226],
    contracts=contracts, compiled_fragments=25, compiled_fragment_lines=131,
    root_all_context_public_and_local_types_read=True, root_branch_and_destructured_types_read=True,
    root_H15_header_token_derivation_verified=True, live_defining_sources=29, exact_cuts=35,
    independent_review_sha256=sha(audit / 'review.json'), private_helpers=[], induction=False,
    proof_body_authorized=True, compiler_authorized=False,
    compiler_activation_requires='Root and independent complete body acceptance and exact early-tool guards',
    whole_goal_complete=False))
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Accepted declaration and source budget\n\nRoot and independent reviews accept the exact public header, all25 fragments,\nbranch/destructured types and the230-line whole-source cap.\nThe header retains the complete H15 packet at one finite specialization and appends Covered.\nOne public theorem, no helper and no induction are authorized.\nA body can now be written. Compiler activation still requires complete body review.\n')
print(json.dumps(dict(status='PASS', contracts=25, compiled_fragment_lines=131,
    source_cap=230, proof_body_authorized=True, compiler_authorized=False)))
