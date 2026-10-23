import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

assert load(HERE / 'root-declaration-review.json')['status'] == 'ROOT_ACCEPTED'
package = Path('/tmp/mcfta-comparison-native-covered-source')
checked_package(package,
    '8573531f2f861b35862ad68eb291437942d9ec2e9007ae8ffbc4b06dced41c55',
    '20c845ad0964eafb4d2bfdbd318e5ebb5c16fe4c10451e3a7c70822dc18c9f06')
audit = Path('/tmp/mcfta-comparison-native-covered-body-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == sys.argv[4]
assert sys.argv[4] in ('CLEAR', 'SOURCE_ONLY_CLEAR')
source = package / (NAME + '.lean')
assert sha(source) == 'c923d6ffba1ccd787aa7384225e34232b5ff3b6098be671355787b982ead3f01'
text = source.read_text()
assert len(text.splitlines()) == 204 <= 230
plan = HERE / 'signature-plan'
positions = []
for item in load(plan / 'insertion-map.json')['compiled_fragments']:
    fragment = (plan / item['file']).read_text().rstrip('\n') + item.get('future_body_attachment', '')
    assert text.count(fragment) == 1
    positions.append(text.index(fragment))
assert positions == sorted(positions)
header = (plan / 'public-header.lean.txt').read_text().rstrip('\n') + ' := by\n'
body = text.split(header, 1)[1]
schema = load(plan / 'declaration-schema.json')
for kind, key in [('have', 'local_have_names'), ('let', 'local_let_names'), ('by_cases', 'by_cases_names')]:
    assert re.findall(r'(?m)^\s*' + kind + r'\s+(\w+)\s*:', body) == schema[key]
assert re.findall(r'(?m)^\s*cases\s+(\w+)\s*:', body) == schema['cases_equation_names']
assert text.count('SourceCurrentSameSymbolEdgeComparisonDomains.original_rows_complete') == 1
assert re.findall(r'(?m)^\s*(?:private\s+)?(?:theorem|def|lemma|abbrev)\s+(\w+)', text) == ['original_rows_complete']
assert not re.search(r'\b(?:sorry|axiom|admit|unsafe|partial|induction|show)\b|set_option', text)
archive(package, 'source')
archive(audit, 'body-audit')
save('selected-source-gate.json', dict(status='ROOT_ACCEPTED', path='lean/MicroCFTA/' + NAME + '.lean',
    snapshot='source/' + NAME + '.lean', sha256=sha(source), lines=204, whole_source_cap=230,
    root_complete_source_read=True, independent_complete_source_review='CLEAR',
    independent_review_sha256=sha(audit / 'review.json'), exact_fragments=25,
    private_helpers=[], induction=False, compiler_activation='STRICT_DEFAULT_LIMITS_ALL_LINTERS',
    proof_jobs_before_activation=0, whole_goal_complete=False))
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Accepted complete proof source\n\nRoot and independent reviews accept the complete204-line source and all25 exact fragments.\nThe source has no helper or induction. It retains one H15 witness and appends native Covered.\nThe next action is the first strict compiler job. No Lean job has run at this gate.\nTwo earlier root declaration-reader metadata failures are retained separately.\n')
print(json.dumps(dict(status='PASS', lines=204, sha256=sha(source), strict_activation=True)))
