exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import difflib

previous = ROOT / 'lean/restart-evidence/20261023-native-node-counter-growth'
package = Path('/tmp/mcfta-demand-node-counter-growth-document-preparation')
assert not package.exists()
package.mkdir()
(package / 'basis').mkdir()
(package / 'patches').mkdir()
basis = (previous / 'update-documents.py').read_text()
selected = basis.replace('a295f1f72153365c886484cbeea933809acbc3f7', START)
selected = selected.replace('audit_build_jobs=3654, audit_dependencies=75556', 'audit_build_jobs=3655, audit_dependencies=75560')
selected = selected.replace('5df4f67bebcf88dfa0bc4a67454a2da1c3cdacebb7be2715271583209da806f7', '255bbf2ca92db811b215e1f915882870c64f3da513c1795c777675aa8e45b541')
selected = selected.replace('public-readback/native-node-counter-growth-', 'full-output/demand-node-counter-growth-')
selected = selected.replace('lean/notes-current-native-node-counter-growth.md', 'lean/notes-current-demand-node-counter-growth.md')
assert selected != basis and len(selected.splitlines()) == len(basis.splitlines()) == 88
(package / 'basis/update-documents.py').write_text(basis)
(package / 'update-documents.py').write_text(selected)
for name, before, after in [('update-documents.py.patch', basis, selected), ('update-documents.py.inverse.patch', selected, basis)]:
    (package / 'patches' / name).write_text(''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile='basis', tofile='selected')))
update = '''## Node-counter growth in checked demand execution

Updated: {now}. Proof checkpoint: `{proof_short}`.
Start: `86b6dd3038`. Imported main remains `794903b3f`.
Read `lean/notes-current-demand-node-counter-growth.md`.

The three checked theorems bound the input node counter by the counter
in the SAME checked-demand step, finite execute or resume outcome state.
They cover yielded, done, failed, constraintError and blocked outcomes.
They permit arbitrary initial states, controls, output types, widths and finite fuel.
The public statements require only the two existing equality instances and inputs.
They have no validity, readiness, success, callback-bound or final-counter premise.
The native-code branch uses H35 step_mono and retains the actual native outcome.
The direct edge branch uses the checked-demand heap observation.
The edge-body branch uses the exact native-state observation.
Fuel induction composes the first bound with the actual yielded control and full state.
Resumption compares the supplied outcome state with the actual resumed state.
No earlier source, constructor order or counterexample changes.
Pair/Scan/H23 lifting, fixed-source initial counter order and original global
domain-history transport remain separate proof targets.
Upper bounds, Room, WordRanges, complete resources, generated execution, Mu/full pass,
practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.

The unchanged 80-line source passed its first strict check with an empty log.
The sole complete public output check passed.
The aggregate Audit passed with 3655 build jobs and 75560 theorem dependency checks.
It replayed one older unused-variable warning. The new source has no warning.
Root and an independent reviewer read all three complete checked public TYPEs.
Actual raw TYPE byte identity and four-ASCII-whitespace lexical identity are true
for all three public theorems. Complete BODY retention was checked programmatically.
The baseline contains 120276 files/modes, 3653 older Lean sources,
298 Haskell files and 207 package files. No Haskell repair was needed.
FINDINGS keeps its external Haskell repair index FIRST.
H35 was pushed and remote-verified at `86b6dd30387c62a1f8f46e1914824695c4a0e908`.
This record precedes the H36 seal and push. It claims neither result.
Standing authorization permits pushing formalize after the verified local seal.
'''
focused = '''# Checked demand node-counter growth

Updated: {now}. Proof checkpoint: `{proof}`.
Start: `86b6dd30387c62a1f8f46e1914824695c4a0e908`.

The theorem step_mono compares the initial physical constructor node counter
with the counter in the actual checked-demand step outcome.
The theorem execute_mono gives the same bound for every finite fuel.
The theorem resume_mono compares the state of a supplied outcome with the state
of its actual resumed outcome. All five checked-demand outcome tags are included.
These tags are yielded, done, failed, constraintError and blocked.

The statements permit arbitrary controls, output types, states, widths and finite fuel.
They require the existing equality instances for Symbol and EdgeKey.
They require no validity, readiness, success, callback-bound or desired-counter premise.
The code branch uses H35 native step_mono on the actual native state.
A private helper proves that lifting each native outcome retains its complete state.
The direct edge branch uses the checked-demand heap observation.
The edge-body branch uses its exact native-state observation.
The fuel induction uses the actual yielded control and full state at predecessor fuel.
No definition, predicate or global instance is added.

The single 80-line variant passed its first strict check under default limits.
All linters were enabled. The strict log is empty.
The sole FULL check retained all 696507 bytes of actual output.
Root and an independent reviewer read the complete checked TYPEs.
All 12 TYPE, printed TYPE, BODY and axiom slices reconstruct the raw log.
BODY retention was checked programmatically. No whole printed BODY read is claimed.
All TYPE pairs have actual raw byte identity and four-ASCII-whitespace lexical identity.
Both raw hashes are retained. All three actual axiom reports contain only
Classical.choice, Quot.sound and propext.
Audit passed with 3655 build jobs and 75560 theorem dependency checks.
One older unused-variable warning was replayed. The new source has no warning.
The complete ledger has three jobs, two source jobs and one Audit job.
It has no failed job, warned source job or rejected public TYPE.

This result gives a node-counter lower bound. It gives no allocation upper bound.
Pair/Scan/H23 lifting, fixed-source initial counter order and global domain-history
transport remain separate. Room, WordRanges, complete resources, generated
execution, Mu/full pass, practical width, Haskell and solver correspondence,
and convergence remain open.
H6 constructed_node_calls remains strongest combined.
The goal is ACTIVE and incomplete.
No Haskell repair is required by this checkpoint.
FINDINGS retains both imported repairs and all earlier evidence.
The baseline contains 120276 files/modes, 3653 older Lean sources,
298 Haskell files and 207 package files.
This note precedes the final seal and push. It claims neither result.
'''
(package / 'current-update.template.md').write_text(update)
(package / 'focused-note.template.md').write_text(focused)
entries = {str(p.relative_to(package)): dict(bytes=p.stat().st_size, sha256=sha(p)) for p in sorted(package.rglob('*')) if p.is_file()}
(package / 'pins.json').write_text(json.dumps(entries, indent=2) + '\n')
(package / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_UNEXECUTED_DOCUMENT_SOURCE_AND_TEMPLATES', pins_sha256=sha(package / 'pins.json')), indent=2) + '\n')
print(json.dumps(dict(package=str(package), pins=sha(package / 'pins.json'), frozen=sha(package / 'FROZEN.json'), writer_lines=88)))
