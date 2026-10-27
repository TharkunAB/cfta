from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-selected-coverage-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
stats = json.loads((area / 'statistics.json').read_text())
public = json.loads((area / 'public-validation.json').read_text())
upstream = json.loads((area / 'final-upstream-refresh.json').read_text())
assert public['status'] == 'pass' and upstream['fetch_exit'] == 0 and upstream['main_is_ancestor']
assert json.loads((area / 'source-validation.json').read_text())['status'] == 'pass'
audit = (area / 'audit-coverage-1/raw.log').read_text()
jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)', audit)[1])
deps = int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA', audit)[1])
prefix = f'''
## Constructive completion from an accepted selected edge

Source checkpoint: {head}.
An accepted current native edge now constructs its actual completed symbolic
edge result under the declared native and resource admission. The proof
derives successful guard projection and inherited arity. It constructs fresh
equality witnesses, prepares the ordered child terms and records the actual
native residual. The final assignment agrees at every old variable, satisfies
the original and returned states, and fills the actual fragment to the term.

The accepted edge wrapper retains the full strengthened resource packet.
Its reservation covers the unique CURRENT pure projection. It takes the
chosen semantic model before its existential work bounds. The retained
primary producer fixes bounds before its universal semantic observer.
Neither theorem takes a desired future success or final assignment as input.
The full caller, memo state, resource forecast, histories and indexes remain.

Forward suspended descent now needs no trie-validity premise. It follows
the actual lookup and filter. Every inherited bucket entry remains required.
Final residual satisfaction uses the actual native guard interpretation.

This closes local selected-edge symbolic coverage. The selector must still
retain an accepting resident edge. Recursive expansion, discharged rendering
coverage, public API admission and physical Haskell correspondence remain
open. H6 and checked finite rendering soundness keep their earlier scopes.
The full formalization goal stays ACTIVE.

Four modules contain {stats['lines']} lines and five public theorems. All new
sources and standalone Audit pass strict checks. Audit passes {jobs} jobs
and checks {deps} theorem dependencies. Public readback contains 168 complete
blocks. All 163 prior blocks and 86 pinned prior sources remain byte exact.
Only the three standard Lean axioms occur. FINDINGS retains every Haskell
repair handoff. Details: `lean/notes-current-selected-coverage.md`.

'''
extra = f'''
### Selected-edge coverage and Haskell repair status

This checkpoint changes Lean proofs only. All earlier Haskell fixes,
regressions and external repair instructions remain below without deletion.
The final successful fetch reads main at {upstream['main']}.
It remains an ancestor with the LPO and extraction documentation fixes.
KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated,
unbuilt and unexecuted. The positive-Int context-reversal finding remains
open. No Haskell source, Cabal file, native test or benchmark changed or ran.
Existing opaque Mu and Union behavior remains a separate expansion and
rendering boundary. No new Haskell defect or runtime repair is claimed.

'''
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
         'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in paths:
    path = root / name
    old = path.read_bytes()
    saved = area / 'prior-documents' / name
    saved.parent.mkdir(parents=True, exist_ok=True)
    assert not saved.exists()
    assert old == subprocess.check_output(['git', 'show', base + ':' + name], cwd=root)
    saved.write_bytes(old)
    offset = old.index(b'\n') + 1
    inserted = (prefix + (extra if name == 'FINDINGS.md' else '')).encode()
    new = old[:offset] + inserted + old[offset:]
    path.write_bytes(new)
    assert new[:offset] + new[offset + len(inserted):] == old
    records.append(dict(path=name, bytes=len(new), sha256=hashlib.sha256(new).hexdigest(),
                        offset=offset, inserted_bytes=len(inserted), prior_bytes=len(old),
                        prior_sha256=hashlib.sha256(old).hexdigest()))
note = f'''# Constructive completion from an accepted current selected edge

Source checkpoint: {head}.
Published base: {base}.
Main: {upstream['main']}. The final successful fetch confirms ancestry.
Previous note: `notes-current-traversal-coverage.md`.

## Target and strongest new statement

The top level target remains correctness of the whole CFTA system. It
includes exact finite-tree transformations, enumeration soundness and
coverage, API behavior and physical Haskell correspondence. Preserve the
optimized interned core, older constructor and equality proofs, all
counterexamples, repairs, marked drafts and restart evidence. The complete
target remains open.

SourcePruningEnumerationSelectedEdge.accepted_complete now starts from
acceptance by the SAME selected native edge, original state Satisfies and
ALL original inherited suspended constraints. The actual parent is available
and closed, and the edge is a member of its resident outgoing list.
The original native Context, Safe, realized storage, roots, correct native
indexes, bounded pending references, Fits and annotation carrier remain
explicit. Reserved capacity covers each successful result of the CURRENT
pure guard projection. That projection has at most one result. This is an
original finite-resource condition, not a future heap or execution gate.

The proof derives the actual successful projection and inherited arity.
It then returns the complete original strengthened resource packet at the
SAME actual result, caller, full final Memos, query table and indexed cache.
A constructed assignment agrees below the original counter and satisfies
both the original and returned states at their respective native heaps.
The actual result completes with a fragment that fills to the accepted term.
A desired extended assignment, successful future run or final satisfaction
is not an input.

Quantifier order is explicit. The accepted wrapper takes the chosen original
model before its existential runtime bounds. It retains the primary
producer's whole result, including a universal semantic observer AFTER
those chosen bounds. The primary complete_with_fragments_resources_accepting
theorem retains its original admission and chooses operational witnesses
before every semantic model. These two scopes are not interchangeable.

## Four proof modules

EnumerationSuspendedForward proves suspended_descent_forward. Its signature
removes only the validity input from the older forward descent theorem.
A private path lemma follows the actual lookup entry back to the original
trie. Membership in the descended trie therefore implies membership of the
prefixed path in the original trie, even with duplicate or invalid entries.
The actual descendScs filter and map introduce no new path. Original parent
Holds supplies each actual child Hold. Backward trie laws retain their
validity premises. No global predicate or data structure is added.

SelectedEdgeAdmission.projected_of_accepted uses current cached equality
annotations. The sourceEqualities=none case rejects every guard term and
contradicts the accepted guard. The successful case derives the actual
projected tries, their validity, own EqualityHolds and native ResidualHolds.
selected_admission obtains that cache premise from the current Context and
actual resident selected edge. Native edgeMeaning supplies the term shape,
ordered child-language relation and guard acceptance. Child-list length and
suspended_arity_necessary derive inherited arity. No future cache is used.

SelectedEdgeCoverage.complete_with_fragments_resources_accepting retains
the entire original SelectedEdgeResources admission and result. It calls
the actual own-class prefix once and the accepting child traversal once.
The projected native guard gives own equalities and the actual residual.
fresh_classes_state_complete constructs equality witnesses at the actual
own-prefix core. It preserves old variables and original restrictions.
Bounded inherited obligations transfer to those witnesses. Forward descent
then supplies every actual inherited-plus-own child bucket, in order.

The accepting traversal constructs a final assignment and actual completed
children. Its agreement below the own counter also preserves fresh equality
witnesses. Original agreement retains original state satisfaction. The
completed parent fragment fills to the accepted constructor term.
finish_semantics records the residual using exactly
fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true.
An arbitrary residual predicate cannot follow from native guard acceptance.
The stopped structural branch keeps its original effects and receipt; an
accepted model would derive an incompatible completed child result.

SelectedEdgeAccepting.accepted_complete derives the projection and allowed
inputs through the admission theorem, invokes the primary producer once,
and applies its observer to the original model. Its entire primary result,
including the uniform observer, remains under an explicit group. It retains
the chosen tries and residual because final resources use their exact cost.
Actual Post and full Memos remain the producer's witnesses. Query equality
never substitutes for equality of the full memo state.

## Verification and preserved attempts

Four modules contain {stats['lines']} lines and {stats['bytes']} source bytes.
They declare five public theorems and no new definition, predicate or
structure. All four installed modules and standalone Audit pass strict
Lean checks with -DwarningAsError=true and -Dlinter.all=true. All recorded
compiler commands run serially at measured 4 GiB memory.max/high and zero
swap. Successful new source strict logs are empty.

Installed helper, admission and primary builds pass 7, 1243 and 1889 jobs.
The complete Audit build includes the accepted wrapper and passes {jobs}
jobs. It checks {deps} theorem dependencies. The old unused-input dependency
warning remains in build logs. Standalone Audit records its expected count.

Public output contains 168 complete signature and axiom blocks. All 163
prior blocks form the exact 592943-byte prefix. All 86 pinned prior source
modules retain their published bytes. Audit adds only four imports; deleting
them recovers the entire old file. Only propext, Classical.choice and
Quot.sound occur. No sorry, admit tactic, custom axiom, native_decide,
heartbeat increase or linter suppression is used. Public output is
{public['bytes']} bytes, SHA256
{public['sha256']}.

Admission v1 and primary v1 were untested drafts. Admission v2 adds an
explicit import and the underlying Symbol alias before its first strict
check. Primary v2 makes the indexed child relation mapping explicit before
its first strict check. That check failed only because simpa only retained
id term in its target. The final primary v3 adds only id_eq at that proof
argument. The full public statement stays byte identical. Its initial
1577-byte strict failure and exact source remain. The second check passes.
The helper and accepted wrapper pass their first strict checks.

Removing only the primary observer and restoring only the theorem name
recovers the entire original 4184-byte producer proposition. The accepted
wrapper retains the entire strengthened result, including its existential
witnesses and observer, with only explicit grouping. Source comparisons,
draft deltas, exact installed snapshots, full logs and inspected source
cuts remain in the evidence.

## Global claims and remaining work

H6 keeps exact accepted finite trees for its covered closed construction,
original guard allocation history and empty inherited payload. Any fixed
finite number of pruning rounds has an actual complete call trace with
sufficient mathematical width and fuel. Convergence and withoutRedundantEdges
remain outside that theorem.

run_initial_finite_render_sound retains finite enumeration soundness from
the literal native startup under its original native Context, initial arity,
resource and policy contracts. Each own output must still be Discharged,
render successfully and pass residual checks. Its rendered term then belongs
to the original root language. These global statements are unchanged here.

The new result closes local SYMBOLIC SELECTED-EDGE coverage. It does not
prove that an arbitrary selector chooses an accepting resident edge.
Current subset and length conditions still admit edgesOf := fun _ => [].
Next connect the resident accepting-edge witness to actual supported
selection and its captured native invocation. Supported pruning callbacks
must retain an equivalent language. Keep each actual caller, full Memos,
captured cache restore and resource history through that composition.

Then derive actual recursive expansion and the required frontier policy.
Fresh Mu and Union still use empty stored buckets and can remain parked.
Constructed finite fragment fillings do not prove full hole unfolding,
Discharged outputs or concrete rendering. Keep the earlier conditional
opaque-boundary observation separate from an instantiated full native
Context/Packet counterexample or a new Haskell defect. Stop and depth
policies remain explicit. Public/native/physical admission, remaining API
obligations and full Haskell correspondence remain open.

No Haskell source or Cabal file changed. No native test or benchmark ran.
Main retains the LPO and extraction documentation fixes. KBO candidate
d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted. The positive-Int context-reversal finding remains open.
FINDINGS retains every previous Haskell repair handoff. The whole goal stays
ACTIVE. No completion percentage or date is claimed.

## Restart evidence

Portable evidence: `restart-evidence/20261027-selected-coverage/`.
The manifest records stored bytes. decoded-files.json records original
bytes for deterministic gzip payloads. Run verify-evidence.py with the
snapshot path. Use --committed after the evidence commit to compare every
payload with Git. Retain all drafts, failed and successful checks, complete
public output, contract comparisons, literal source cuts, final reviews and
all nine original document bodies. Keep publication receipts outside the
frozen TEMP area and archive. Earlier frozen evidence remains unchanged.
'''
name = 'lean/notes-current-selected-coverage.md'
path = root / name
assert not path.exists()
path.write_text(note)
paths.append(name)
records.append(dict(path=name, bytes=len(path.read_bytes()),
                    sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(paths, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(paths), preserved_prior_documents=9,
                      note_bytes=len(path.read_bytes()), source_head=head)))
