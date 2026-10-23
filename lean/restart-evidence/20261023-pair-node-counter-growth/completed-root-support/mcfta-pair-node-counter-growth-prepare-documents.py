exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast
import datetime
import difflib

target = Path('/tmp/mcfta-pair-node-counter-growth-document-preparation')
assert not target.exists()
target.mkdir()
basis = (ROOT / 'lean/restart-evidence/20261023-demand-node-counter-growth/update-documents.py').read_text()
replacements = [
    ('86b6dd30387c62a1f8f46e1914824695c4a0e908',START),
    ('public_theorems=3, audit_build_jobs=3655, audit_dependencies=75560','public_definitions=1, public_theorems=2, audit_build_jobs=3656, audit_dependencies=75572'),
    ('255bbf2ca92db811b215e1f915882870c64f3da513c1795c777675aa8e45b541','18eebc67eff772ba1d8b6ce6f87caf8765b9abc83e5f4c4e50356ef0a7585665'),
    ('full-output/demand-node-counter-growth','full-readback/pair-node-counter-growth'),
    ('notes-current-demand-node-counter-growth','notes-current-pair-node-counter-growth')]
selected = basis
for old,new in replacements:
    assert selected.count(old) > 0
    selected = selected.replace(old,new)
restored = selected
for old,new in reversed(replacements):
    restored = restored.replace(new,old)
assert restored == basis
assert len(selected.splitlines()) == 88 <= 100
assert sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(selected))) == 25
(target / 'basis.py.txt').write_text(basis)
(target / 'update-documents.py').write_text(selected)
(target / 'writer.patch').write_text(''.join(difflib.unified_diff(basis.splitlines(True),selected.splitlines(True),fromfile='basis/update-documents.py',tofile='selected/update-documents.py')))
(target / 'writer.inverse.patch').write_text(''.join(difflib.unified_diff(selected.splitlines(True),basis.splitlines(True),fromfile='selected/update-documents.py',tofile='basis/update-documents.py')))
(target / 'literal-recipe.json').write_text(json.dumps(replacements,indent=2)+'\n')
update = '''## Node-counter growth in pair comparison

Updated: {now}. Proof checkpoint: `{proof_short}`.
Start: `de085728eb`. Imported main remains `794903b3f`.
Read `lean/notes-current-pair-node-counter-growth.md`.

The public outcomeState returns the complete pair State from all five outcomes.
It requires no equality instance. The two counter theorems use only the existing instances.
They bound the input constructor node counter by the counter in the SAME actual
pair step or finite execute outcome state, for arbitrary states, controls, widths and fuel.
They cover yielded, done, failed, constraintError and blocked outcomes.
They have no validity, readiness, success, callback-bound or final-counter premise.
Memo call, demand, order and return phases retain the checked state.
The native phase uses H36 step_mono at the same body and checked state.
Fuel induction uses only the actual yielded next control and complete after state.
No earlier source, constructor order or counterexample changes.
Lifting this counter bound through Scan/H23, fixed-source initial counter order
and transport of the original global domain history remain separate targets.
Earlier H23 completion and language-preservation results remain proved under their premises.
Upper bounds, full-pipeline Room/WordRanges and complete resources, generated execution,
Mu/full pass, practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.

The unchanged 96-line source passed its first strict check with an empty log.
The sole complete public output check passed.
The aggregate Audit passed with 3656 build jobs and 75572 theorem dependency checks.
It replayed one older unused-variable warning. The new source has no warning.
Root and an independent reviewer read all three complete checked public TYPEs.
Actual raw TYPE byte identity is false for the accessor and true for both theorems.
All three four-ASCII-whitespace lexical identities are true. Both raw hashes are retained.
The accessor has no axioms. The theorems use only the three allowed standard axioms.
Complete BODY retention and raw reconstruction were checked programmatically.
The baseline contains 122017 files/modes, 3654 older Lean sources,
298 Haskell files and 207 package files. No Haskell repair was needed.
FINDINGS keeps its external Haskell repair index FIRST.
H36 was pushed and remote-verified at `de085728ebe1e905ae339eaba8d26348126e5ada`.
This record precedes the H37 seal and push. It claims neither result.
Standing authorization permits pushing formalize after the verified local seal.
'''
focused = '''# Pair comparison node-counter growth

Updated: {now}. Proof checkpoint: `{proof}`.
Start: `de085728ebe1e905ae339eaba8d26348126e5ada`.

The public outcomeState returns the complete actual pair State from every outcome.
The step_mono and execute_mono theorems bound the input constructor node counter
by the counter in that actual outcome state. They allow arbitrary states, controls,
widths and finite fuel. They include yielded, done, failed, constraintError and blocked.
The accessor has no equality instance or axioms. Only the two existing equality
instances occur on the theorem heads. No validity, readiness, success, callback bound
or final-counter premise is required.

Memo publication, all four demand observations, ordering and return retain checked.
The native phase uses H36 at the same body and checked state. It forwards the exact
returned checked state for each outcome. The fuel induction generalizes control
and the complete pair state. Its only IH call is ih next after at predecessor fuel.
The public control has no resume operation. This module adds no resume theorem.

The unchanged 96-line source passed its first strict check with an empty log.
The sole FULL job passed and retained 1048134 raw bytes.
Root and an independent reviewer read all checked public TYPEs: 2, 35 and 35 lines.
All twelve retained slices reconstruct the complete raw output.
BODY retention was checked programmatically. No whole manual BODY review is claimed.
Raw TYPE byte identity is false for outcomeState and true for both theorems.
All three lexical identities are true. The accessor axiom set is empty.
Both theorem axiom sets contain only Classical.choice, Quot.sound and propext.
The aggregate Audit passed with 3656 build jobs and 75572 dependency checks.
It replayed the older unused-input warning. The new source has no warning.

The actual history has three successful proof jobs, one unchanged mathematical
variant, zero source patches and zero rejected public TYPEs. The collector cut
retains 1176 artifacts and eighteen successful metadata attempts. Final support
retains the collector receipt and later receipts outside that historical cut.
The declaration Observation-type parentheses correction and the added actual FULL
selection link are metadata corrections. Their original bytes remain retained.
No Haskell repair was needed. No older source, draft, counterexample or optimized core changes.

Lifting this counter bound through Scan/H23, fixed-source initial counter order
and transport of the original global domain history remain separate targets.
The earlier H23 conditional completion and language-preservation results remain proved.
Upper bounds, full-pipeline Room/WordRanges and complete resources, generated execution,
Mu/full pass, practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
The next mathematical target is the actual cluster-scan counter bound.
This note precedes the H37 seal and push. It claims neither result.
'''
(target / 'current-update.template.md').write_text(update)
(target / 'focused-note.template.md').write_text(focused)
(target / 'source-review-facts.json').write_text(json.dumps(dict(status='SELECTED_SOURCE_ONLY_NO_WRITER_EXECUTION',writer_lines=88,assertions=25,
    writer_sha256=sha(target / 'update-documents.py'),scope_gate_sha256=sha(HERE / 'root-document-scope-gate.json'),
    selected_hard_stop=100,all_25_guards_retained=True,nine_exact_LF_inverses=True,FINDINGS_repair_index_first=True,
    actual_both_saved_modes_and_proof_commit_required_at_runtime=True,
    future_seal_push_claimed=False,older_H23_results_preserved=True),indent=2)+'\n')
files = {str(path.relative_to(target)):dict(bytes=path.stat().st_size,sha256=sha(path)) for path in sorted(target.rglob('*')) if path.is_file()}
(target / 'pins.json').write_text(json.dumps(files,indent=2)+'\n')
(target / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_SELECTED_DOCUMENT_SOURCE_AND_PROPOSED_PAYLOADS',observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),pins_sha256=sha(target / 'pins.json'),payloads=len(files)),indent=2)+'\n')
print(json.dumps(dict(status='FROZEN',path=str(target),pins_sha256=sha(target / 'pins.json'),frozen_sha256=sha(target / 'FROZEN.json'),writer_sha256=sha(target / 'update-documents.py'))))
