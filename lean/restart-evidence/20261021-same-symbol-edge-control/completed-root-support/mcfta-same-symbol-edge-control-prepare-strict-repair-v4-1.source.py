import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
before = (HERE / 'same-symbol-edge-strict-1.source.lean').read_text()
assert hashlib.sha256(before.encode()).hexdigest() == '89ceb64ea5bc18f5a2c712a8764e345398344113519ec7d6516724847e17bb6a'
assert json.loads((HERE / 'same-symbol-edge-strict-1.json').read_text())['exit_code'] == 1
target = Path('/tmp/mcfta-same-symbol-edge-control-strict-repair-v4')
assert not target.exists()
source = before
edits = [
    ('''    simpa only [step, pairKey, allocated.1] using
      (rfl : step (.call request pending) before = step (.call request pending) before)''',
     '''    change Outcome.yielded
      (.demand (FlatMemoThunk.lookupOrInsert (pairKey request) request before.memo).1 pending)
      {before with memo := published} = _
    exact congrArg (fun handle => Outcome.yielded (.demand handle pending)
      {before with memo := published}) allocated.1'''),
    ('''      simpa only [Cache.put, ite_eq_right different] using reverseMissing''',
     '''      rw [Cache.put, if_neg different]
      simpa only [pairKey] using reverseMissing'''),
    ('''      simp only [table, Cache.put, ite_eq_left rfl]''', '''      simp [table, Cache.put]'''),
    ('''      simp only [nextTable, Cache.put, ite_eq_left rfl]''', '''      simp [nextTable, Cache.put]'''),
    ('''      simpa only [memo, finish_table, pairKey, Cache.put, ite_eq_left rfl] using stored''',
     '''      simpa [memo, finish_table, pairKey, Cache.put] using stored'''),
    ('''      exact False.elim (reversed impossible)''', '''      exact False.elim impossible'''),
]
for old, new in edits:
    assert source.count(old) == 1, old
    source = source.replace(old, new)
assert source.split('private abbrev Memo', 1)[0] == before.split('private abbrev Memo', 1)[0]
header = source[source.index('theorem miss_readback'):].split(' := by\n', 1)[0] + '\n'
assert header == (HERE / 'control-author-v2/proposed-signature.lean.txt').read_text()
assert len(source.splitlines()) <= 400
target.mkdir()
(target / 'SourceCurrentSameSymbolEdgeControl.lean').write_text(source)
(target / 'failed-strict1-source.lean.txt').write_text(before)
(target / 'proof-only.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True), source.splitlines(True),
    fromfile='failed-strict1-source.lean.txt', tofile='SourceCurrentSameSymbolEdgeControl.lean')))
(target / 'note.md').write_text('SOURCE-ONLY proof repair after actual strict1 terminal exit1.\n'
    'The first check reported six errors and two unused simp arguments. Its full source, log, caps and receipt remain.\n'
    'Use congrArg for the lookup handle, unfold pairKey explicitly, close true conditionals with simp, and eliminate the already-false premise directly.\n'
    'All public API, interpreter, context and theorem header bytes remain unchanged. No limits or linter exceptions change.\n'
    'Root and independent whole-source review must precede strict2. No FULL has run.\n')
report = dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(), source_lines=len(source.splitlines()),
    failed_source_sha256=hashlib.sha256(before.encode()).hexdigest(), header_exact=True,
    interpreter_and_api_exact=True, actual_Lean_jobs_so_far=1, FULL_jobs_so_far=0)
(target / 'source-proposal.json').write_text(json.dumps(report, indent=2) + '\n')
(target / 'pins.json').write_text(json.dumps({p.name: hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(target.iterdir())}, indent=2) + '\n')
print(json.dumps(report))
