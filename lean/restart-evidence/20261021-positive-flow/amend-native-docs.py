from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
old = (HERE / 'current-update.md').read_text()
paragraph = '''A constructed native counterexample now excludes unrestricted support
for this opaque-Mu observer. Two actual closed source Mu inputs have no
PositiveAt occurrence. Native execution from empty result tables returns
a positive ordinary row. Native support needs genuine exposure premises
or a stronger observer. This is not a Haskell runtime defect.

'''
new = old.replace('Root strict and complete component readback pass.',
    paragraph + 'Root strict and complete component readback pass.')
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
             'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
             'lean/notes-current-system-claim.md']:
    path = ROOT / name
    content = path.read_text()
    assert content.count(old) == 1, name
    path.write_text(content.replace(old, new, 1))
(HERE / 'current-update.md').write_text(new)
old = (HERE / 'findings-update.md').read_text()
new = old.replace('No Haskell source, runtime result or external fix changes.',
    paragraph + 'No Haskell source, runtime result or external fix changes.')
path = ROOT / 'FINDINGS.md'
content = path.read_text()
assert content.count(old) == 1
path.write_text(content.replace(old, new, 1))
(HERE / 'findings-update.md').write_text(new)
path = ROOT / 'lean/notes-current-positive-flow.md'
content = path.read_text()
content = content.replace('The main next task is actual positive-position support for Merge.', '''## Checked native observer boundary

The constructed actual_opaque_mu_counterexample starts from a closed
source build. Its two distinct available full Mu operands have closed
unused bodies. PositiveAt deliberately has no constructor for Mu, so
neither operand has an occurrence at any path. The actual native driver
starts with empty node and edge result tables. execute 64 returns an
ordinary node with a nonplain root row and PositiveAt result [].
An actual admitted physical Trace retains that same execution.
The source builder really retains both raw Mu binders.
This refutes an unrestricted native positional law for the current
observer, even with physical Good, available operands and empty tables.
It does not refute a law with the required Plain-cap/exposure premises.
It does not assert a selected outer trace for these operands.
It is a model execution, not a production Haskell runtime result.
All failed elaborations, strict receipts and full readback remain.

## Remaining Merge and native support

The main next task is actual positive-position support for Merge.''', 1)
path.write_text(content)
