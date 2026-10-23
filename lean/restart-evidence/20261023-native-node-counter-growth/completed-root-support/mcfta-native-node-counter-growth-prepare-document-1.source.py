exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import datetime
import difflib
owner = Path('/tmp/mcfta-native-node-counter-growth-document-preparation')
owner.mkdir()
basis = ROOT / 'lean/restart-evidence/20261023-stored-node-counter-growth/update-documents.py'
original = basis.read_text()
selected = original
for before, after in [
    ('af73f5d67493168cbab9cdd58cbc625d80585a23', START),
    ('audit_build_jobs=3653, audit_dependencies=75553', 'audit_build_jobs=3654, audit_dependencies=75556'),
    ('e077c7b1d57b104aae5c1458febcff0b1a244e60e0c2d3519a798fae6ea25d8a', '5df4f67bebcf88dfa0bc4a67454a2da1c3cdacebb7be2715271583209da806f7'),
    ('lean/notes-current-stored-node-counter-growth.md', 'lean/notes-current-native-node-counter-growth.md')
]:
    assert selected.count(before) == 1
    selected = selected.replace(before, after, 1)
assert selected.count('public-readback/stored-node-counter-growth-') == 3
selected = selected.replace('public-readback/stored-node-counter-growth-', 'public-readback/native-node-counter-growth-')
assert len(original.splitlines()) == len(selected.splitlines()) == 88
(owner / 'update-documents.py').write_text(selected)
(owner / 'update-documents.py.basis.txt').write_text(original)
for name, before, after in [('update-documents.py.patch', original, selected), ('update-documents.py.inverse.patch', selected, original)]:
    (owner / name).write_text(''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile='before/update-documents.py', tofile='after/update-documents.py')))
update = '''## Node-counter growth in native execution

Updated: {now}. Proof checkpoint: `{proof_short}`.
Start: `a295f1f721`. Imported main remains `794903b3f`.
Read `lean/notes-current-native-node-counter-growth.md`.

The three checked theorems bound the input node counter by the counter
in the SAME native step, finite execute or resume outcome state.
They cover yielded, done, failed and blocked outcomes.
They permit arbitrary initial native states, code, widths and finite fuel.
The public statements require only the two existing equality instances and inputs.
They have no validity, readiness, success, callback-bound or final-counter premise.
Work uses the actual reservation count. Optional binders use H34 maybeMu_mono.
The pending constructor case retains the actual returned heap.
Native node and edge observations use public immediate machine equalities.
Fuel induction composes the first bound with the actual yielded code and full state.
Resumption compares the supplied outcome state with the actual resumed state.
No earlier source, constructor order or counterexample changes.
Scan/H23 lifting, fixed-source initial counter order and original global
domain-history transport remain separate proof targets.
Upper bounds, Room, WordRanges, complete resources, generated execution, Mu/full pass,
practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.

The unchanged 79-line source passed its first strict check with an empty log.
The sole complete public output check passed.
The aggregate Audit passed with 3654 build jobs and 75556 theorem dependency checks.
It replayed one older unused-variable warning. The new source has no warning.
Root and an independent reviewer read all three complete checked public TYPEs.
Lexical TYPE identity and complete BODY retention were checked programmatically.
Actual raw TYPE byte identity is true for step and false for execute and resume.
Both raw TYPE hashes are retained. The differences contain only whitespace.
The baseline contains 118574 files/modes, 3652 older Lean sources,
298 Haskell files and 207 package files. No Haskell repair was needed.
FINDINGS keeps its external Haskell repair index FIRST.
H34 was pushed and remote-verified at `a295f1f72153365c886484cbeea933809acbc3f7`.
This record precedes the H35 seal and push. It claims neither result.
Standing authorization permits pushing formalize after the verified local seal.
'''
focused = '''# Native node-counter growth

Updated: {now}. Proof checkpoint: `{proof}`.
Start: `a295f1f72153365c886484cbeea933809acbc3f7`.

The theorem step_mono compares the initial physical constructor node counter
with the counter in the actual native step outcome.
The theorem execute_mono gives the same bound for every finite fuel.
The theorem resume_mono compares the state of a supplied outcome with the state
of its actual resumed outcome. All four native outcome tags are included.

The statements permit arbitrary code, states, widths and finite fuel.
They require the existing equality instances for Symbol and EdgeKey.
They require no validity, readiness, success, callback-bound or desired-counter premise.
The proof uses actual Work reservations and the H34 optional-binder bound.
Pending constructor work uses its actual returned heap.
The fuel induction uses the actual yielded code and state at predecessor fuel.
No private helper, definition or predicate is added.

The single 79-line variant passed its first strict check under default limits.
All linters were enabled. The strict log is empty.
The sole FULL check retained all 214732 bytes of actual output.
Root and an independent reviewer read the complete checked TYPEs.
All 12 TYPE, printed TYPE, BODY and axiom slices reconstruct the raw log.
BODY retention was checked programmatically. No whole printed BODY read is claimed.
All TYPE pairs are equal after four-ASCII-whitespace normalization.
Their actual raw byte identity flags are true, false and false, in public order.
Both raw hashes are retained. All three actual axiom reports contain only
Classical.choice, Quot.sound and propext.
Audit passed with 3654 build jobs and 75556 theorem dependency checks.
One older unused-variable warning was replayed. The new source has no warning.
The complete ledger has three jobs, two source jobs and one Audit job.
It has no failed job, warned source job or rejected public TYPE.

This result gives a node-counter lower bound. It gives no allocation upper bound.
Scan/H23 lifting, fixed-source initial counter order and global domain-history
transport remain separate. Room, WordRanges, complete resources, generated
execution, Mu/full pass, practical width, Haskell and solver correspondence,
and convergence remain open.
H6 constructed_node_calls remains strongest combined.
The goal is ACTIVE and incomplete.
No Haskell repair is required by this checkpoint.
FINDINGS retains both imported repairs and all earlier evidence.
The baseline contains 118574 files/modes, 3652 older Lean sources,
298 Haskell files and 207 package files.
This note precedes the final seal and push. It claims neither result.
'''
for name, text in [('current-update.template.md', update), ('focused-note.template.md', focused)]:
    assert text.endswith('\n') and '\r' not in text
    (owner / name).write_text(text)
(owner / 'scope.md').write_text('The complete H34 writer has 88 lines. Only START, actual Audit counts/hash, readback prefix and focused-note path change. All generic guards remain. Both saved proof modes and the exact two-file proof commit must precede all nine additive LF updates. FINDINGS keeps its repair index first. The templates state only the native node-counter lower bound and actual verification. No program has run.\n')
pins = [dict(path=str(path.relative_to(owner)), bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.rglob('*')) if path.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_SOURCE_ONLY_REVIEW_REQUIRED',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), pins_count=len(pins),
    pins_sha256=sha(owner / 'pins.json'), selected_writer_lines=88, no_execution=True), indent=2) + '\n')
print(json.dumps(dict(owner=str(owner), pins_sha256=sha(owner / 'pins.json'), FROZEN_sha256=sha(owner / 'FROZEN.json'))))
