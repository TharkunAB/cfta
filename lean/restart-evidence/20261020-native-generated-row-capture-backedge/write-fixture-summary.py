import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
selection = json.loads((HERE / 'capture-fixture/backedge-kernels-selection.json').read_text())
assert selection['finalized']
strict = json.loads((HERE / 'root-backedge-fixture-strict-1.json').read_text())
assert strict['exit_code'] == 0 and not (HERE / 'root-backedge-fixture-strict-1.log').read_bytes()
assert strict['sha256'] == '1f3d2f37c7ab4de22dc9c6ad81230fdf27a98015e86b5cfd0b90ec79387e0d76'
summary = '''The new union-body example runs an actual admitted native prefix of
60 steps. Its actual optional operation creates a new used outer Mu.
The same returned callback row forces variable slot two, original pool
slot one and one binder crossing. The captured full Mu was in the
original heap. Its same returned earlier-generation arm contradicts
actual prefix growth and its missing-cell receipt. The initial arm
retains the same original indexed path and ultimate node RowCall for
the complete tag17/Top/nullary stored row. All generic clauses remain.
No actual unfold is run by this example.
'''
(HERE / 'fixture-summary.md').write_text(summary)
detail = '''## Concrete actual generated capture

The sole constructed public declaration is
GeneratedRowCaptureBackedgeFixture.actual_generated_initial_capture_backedge.
Its source has 1407 lines and SHA256
1f3d2f37c7ab4de22dc9c6ad81230fdf27a98015e86b5cfd0b90ec79387e0d76.

The new source family has two distinct used outer binders and one shared
used inner binder. Each outer body is a union. One member has an outerRec
self row and a distinct side tag. The other member is the shared inner
Mu. The inner body has its own innerRec self row and a nullary tag17 row.
All source fields are Top. The original pair node contains the two outers.
Initial validity, native memo History, resource admission and available
operands follow from this actual closed source build.

Checked local arithmetic bridges let cbv evaluate direct Nat operations
through the standard overloaded operations. The bridges are rfl theorems.
They change only proof reduction. The exact locator returns 60, and the
actual finite execute prefix reaches the requested outer optional site.
The actual maybeMu completes. Its target full cell is absent before the
operation and present afterward. Its stored body uses its own interned
reference. The input leaves pool is nonempty and contains the shared
initial full Mu at occurrence one.

The example derives the exact generated build and rooted writer from
the actual optional operation and its records. The public of_written
adapter supplies Stored. Actual source_trace and optional publication
history supply the semantic and causal support for Observed. No desired
terminal, writer identity, future successful return or rank is supplied.

The example calls generated_row_capture_backedge once. It keeps the
same returned event, raw callback and all generic stored and unfold
clauses. Finite Reached classification fixes the only binder body.
The actual node RowCall symbol excludes the tag17 row from the outerRec
node alternative. The generic size bound excludes the root binder
alternative. The same returned capture therefore has variable slot two,
original slot one and one crossing. Its exact full payload is the shared
initial Mu. Actual prefix growth and the earlier arm's missing cell
exclude that arm. The same initial arm retains its full indexed original
path and ultimate original node RowCall for this complete stored row.

The example does not execute an unfold. The generic conditional unfold
clauses remain. It adds one validated union-body source family. Earlier
union variants and the unary-inner exploratory variant remain unselected.
Depth failures, deliberately open diagnostic goals and capped memory
failures are retained. They establish no native execution counterexample.

'''
path = ROOT / 'lean/notes-current-native-generated-row-capture-backedge.md'
text = path.read_text()
assert '## Concrete actual generated capture\n' not in text
path.write_text(text.replace('## Exact public contract\n', detail + '## Exact public contract\n', 1))
print(json.dumps({'status': 'PASS', 'constructed_examples': 1, 'actual_native_steps': 60}))
