exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import re
import sys
name = 'SourceCurrentOriginalRowClusterAdmissionBoundary'
owner = Path('/tmp/mcfta-cluster-admission-boundary-source-v1')
review = Path('/tmp/mcfta-cluster-admission-boundary-body-audit')
checked_package(owner, '9c0319c74e8739c2c5d29515bd12b448c937e8b4981ce3e61a514a3347d74059', '909dfbed0d2e4a74b3b76c664fbc457a9fed24204cdc4904964515bf873bff23')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
source = owner / (name + '.lean')
assert sha(source) == 'b4e42c8340609516e7dc410580734152184daf48bf60146343dcee846fccc1a9'
text = source.read_text()
body = text.split(' := by\n', 1)[1]
assert len(text.splitlines()) == 199
assert not re.search(r'\b(sorry|axiom|admit|native_decide|set_option)\b', text)
schema = load(HERE / 'boundary-declaration-plan/declaration-schema.json')
assert re.findall(r'^\s*(?:·\s*)?have (\w+)\s*:', body, re.M) == schema['local_have_names']
assert re.findall(r'^\s*(?:·\s*)?let (\w+)\s*:', body, re.M) == schema['local_let_names']
assert re.findall(r'^\s*by_cases (\w+)\s*:', body, re.M) == schema['by_cases_names']
assert body.count('induction ') == 1
assert load(HERE / 'root-boundary-declaration-gate.json')['whole_source_hard_stop'] == 230
assert load(HERE / 'root-execution-full-review.json')['status'] == 'ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED'
assert load(HERE / 'execution-build1.json')['exit_code'] == 0
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentOriginalRowClusterExecution.lean') == 'ee67ecabee46dd20e570eba723a816849c6d28f31a9e14d794eb4026a56092bb'
assert (ROOT / 'lean/.lake/build/lib/lean/MicroCFTA/SourceCurrentOriginalRowClusterExecution.olean').exists()
archive(owner, 'boundary-source-v1')
archive(review, 'boundary-body-audit')
save('root-boundary-body-gate.json', {
    'status': 'ACCEPTED_SOURCE_BODY_FOR_STRICT', 'source_sha256': sha(source), 'source_lines': 199,
    'root_complete_source_read': True, 'root_complete_contracts_and_IH_read': True,
    'independent_body_review_sha256': sha(review / 'review.json'),
    'ops_exact_source_installed_and_focused_build_passed': True,
    'strict_compiler_activation_authorized': True, 'FULL_activation_authorized': False,
    'default_declaration_limits': True, 'all_linters': True,
    'metadata_gate_repair': 'The first gate scan counted public let rows. The second gate scopes local declarations to the body. The failed gate snapshot and receipt remain; mathematical source and review are unchanged.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: complete199-line boundary accepted for first strict default-limits check')
