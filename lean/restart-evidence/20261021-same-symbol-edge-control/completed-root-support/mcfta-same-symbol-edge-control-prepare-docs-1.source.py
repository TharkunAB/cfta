import difflib
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
before = (HERE / 'control-author-v2/SourceCurrentSameSymbolEdgeControl.lean').read_text()
assert hashlib.sha256(before.encode()).hexdigest() == '957d1fd8e9bcead6bd2ced0fc85611b26d2f5356809d18884ac088d7de687533'
target = Path('/tmp/mcfta-same-symbol-edge-control-documented-v3')
assert not target.exists()
source = before
module = '''
/-!
# Same-symbol edge comparison

Publish the original pair before demand and numeric operand ordering.
Keep the pair memo separate from the native memo tables.
A completed miss supplies its body trace and captured operands.
Completion and semantic intersection require separate proofs.
-/
'''
context_end = 'variable {width : Nat}\n'
assert source.count(context_end) == 1
source = source.replace(context_end, context_end + module)
docs = {
    'structure State (width : Nat)': 'A comparison retains the complete checked state and a separate pair memo.',
    '  checked : SourceEqualityNativeDemand.State width': 'Retain the native machine and all equality operation caches.',
    '  memo : FlatMemoThunk.State': 'Store the captured operand pair and its eventual returned edge.',
    'inductive Control : Type 1': 'Each phase retains the handles that must receive the returned edge.',
    '  | call (request': 'Publish the original pair before demand.',
    '  | demand (handle': 'Observe the captured cell without replacing its request.',
    '  | order (handle': 'Order the captured operands after publication and demand.',
    '  | native (control': 'Execute the existing native body with its complete checked state.',
    '  | ret (value': 'Finish each pending pair cell with the actual returned edge.',
    'inductive Blocked where': 'Pair-memo blockages remain distinct from native blockages.',
    '  | absent (handle': 'Report a handle with no allocated cell.',
    '  | busy (handle': 'Report a cell that is already under evaluation.',
    '  | native (reason': 'Report the original native blockage.',
    'inductive Outcome (width': 'Every outcome retains the actual current state.',
    '  | yielded (control': 'Retain the next control and its full state.',
    '  | done (value': 'Return the completed edge and its full state.',
    '  | failed (reason': 'Retain the native failure and its full state.',
    '  | constraintError (message': 'Retain the constraint error and its full state.',
    '  | blocked (reason': 'Retain the blockage, exact remaining control and full state.',
    'noncomputable def step ': 'Advance one pair-memo or native step without resetting either state.',
    'noncomputable def execute ': 'Run at most the supplied number of control steps.',
    'theorem miss_readback ': 'Read the native trace and completed pair cells from a successful miss.',
}
for key, doc in docs.items():
    assert source.count(key) == 1, key
    indent = '  ' if key.startswith('  ') else ''
    source = source.replace(key, indent + '/-- ' + doc + ' -/\n' + key)
strip = lambda text: re.sub(r'/\-.*?\-/', '', text, flags=re.S)
assert ''.join(strip(source).split()) == ''.join(strip(before).split())
assert source.startswith((HERE / 'control-author-v2/proposed-context.lean.txt').read_text())
header = source[source.index('theorem miss_readback'):].split(' := by\n', 1)[0] + '\n'
assert header == (HERE / 'control-author-v2/proposed-signature.lean.txt').read_text()
assert len(source.splitlines()) <= 400
target.mkdir()
(target / 'SourceCurrentSameSymbolEdgeControl.lean').write_text(source)
(target / 'source-v2.lean.txt').write_text(before)
(target / 'documentation-only.patch').write_text(''.join(difflib.unified_diff(
    before.splitlines(True), source.splitlines(True), fromfile='source-v2.lean.txt',
    tofile='SourceCurrentSameSymbolEdgeControl.lean')))
(target / 'note.md').write_text('SOURCE-ONLY v3. Add documentation for public types, fields, constructors and operations.\n'
    'All non-comment tokens, the first10 context lines and the exact public header remain unchanged.\n'
    'No Lean job has run. Whole root and independent review must precede an ordinary check.\n'
    'The earlier inline preparation stopped before writing a candidate: its raw header substring check included a final newline before the inline proof separator.\n'
    'This preparation extracts the header at the actual proof separator. It does not weaken the required header byte comparison.\n')
report = dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(), source_lines=len(source.splitlines()),
    original_sha256=hashlib.sha256(before.encode()).hexdigest(), non_comment_tokens_identical=True,
    context_exact=True, header_exact=True, lean_jobs=0)
(target / 'source-proposal.json').write_text(json.dumps(report, indent=2) + '\n')
pins = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(target.iterdir())}
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps(report))
