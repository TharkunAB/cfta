from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
proof = (HERE / 'proof-commit.txt').read_text().strip()
old = (HERE / 'current-update.md').read_text()
paragraph = '''Actual safe Required success now preserves each positive ordinary-row
occurrence backwards at the SAME natural child-index path. Row choices
may change. Literal unions add no path component. Mu bodies and references
remain opaque. The theorem consumes the actual fuelled return equation.

'''
new = old.replace('`3b1141c4b`', '`' + proof[:9] + '`').replace('02:04 CEST', '02:08 CEST')
new = new.replace('All three root strict checks', paragraph + 'All four root strict checks')
new = new.replace('3554 jobs and 74418', '3555 jobs and 74422')
new = new.replace('The two elaboration failures', 'The three elaboration failures')
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
             'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
             'lean/notes-current-system-claim.md']:
    path = ROOT / name
    content = path.read_text()
    assert content.count(old) == 1, name
    path.write_text(content.replace(old, new, 1))
(HERE / 'current-update.md').write_text(new)
old = (HERE / 'findings-update.md').read_text()
new = old.replace('`3b1141c4b`', '`' + proof[:9] + '`').replace('02:04 CEST', '02:08 CEST')
new = new.replace('Three root strict logs', paragraph + 'Four root strict logs')
new = new.replace('3554 jobs and 74418', '3555 jobs and 74422')
path = ROOT / 'FINDINGS.md'
content = path.read_text()
assert content.count(old) == 1
path.write_text(content.replace(old, new, 1))
(HERE / 'findings-update.md').write_text(new)
path = ROOT / 'lean/notes-current-support-foundations.md'
content = path.read_text().replace('3b1141c4b3742f6c70a7af4722ed018cb9050428', proof)
content = content.replace('02:04 CEST', '02:08 CEST')
content = content.replace('## Validation\n', '''SourceCurrentRequiredPositivePosition.PositiveAt addresses nonplain ordinary
rows at natural child-index paths. Ordinary row indices remain explicit
choices. Literal union choices add no path component. Mu bodies and
references stay opaque. not_plain excludes this relation in a hereditary
Plain region. origin proves same-path backwards support through actual
indexed Required origins. required consumes the literal fuelled
SourceEqualityRequiredWorker.require return equality. Existing soundness
and the exact semantic, cost, availability, GuardHeap Plain and ExposureSafe
premises derive that origin. It introduces no native schedule, false gate,
closedness or observational Mu unfolding premise. This closes the first
preparation stage of the positional support argument. Required for a whole
forest, Merge, native effects and chronological class edits still need
their corresponding actual support laws.

## Validation
''', 1)
content = content.replace('All three independent', 'All four independent')
content = content.replace('3554 jobs and 74418', '3555 jobs and 74422')
content = content.replace('Combined has one head, geometry three, and Empty support four.',
    'Combined has one head, geometry three, Empty support four, and Required four.')
content = content.replace('Two failed elaborations remain.', 'Three failed elaborations remain.')
content = content.replace('the three imports', 'the four imports')
path.write_text(content)
