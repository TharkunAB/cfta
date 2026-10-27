from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-traversal-coverage-20261027')
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
## Constructive coverage of ordered native child traversal

Source checkpoint: {head}.
The actual ordered child traversal now completes for every accepted ordered
term list under the original native and resource admission. Each term must
satisfy every original suspended constraint in its input bucket, under an
original satisfying assignment. The proof constructs a final assignment
that agrees at every original allocated variable. It satisfies the original
and returned states. Filling the actual returned fragments gives exactly
the supplied terms in order. All work bounds precede these semantic inputs.

Each child supplies the actual caller, cache, full memo state and resources
for the next child. Later fresh assignments preserve earlier fillings at
the counter reached by the earlier child. The full old traversal packet
remains, including stopped prefixes, protection, pending references and
the original mixed reservation. No future success or assignment is supplied.

This closes ordered symbolic child-preparation coverage. Parent-edge
selection, projected equality witnesses, recursive expansion and rendering
coverage remain open. Semantic selector and pruning contracts, public API
admissions and physical Haskell correspondence also remain open. H6 exact
finite-tree preservation and checked finite rendering soundness retain
their earlier scopes. The full formalization goal stays ACTIVE.

One module contains {stats['lines']} lines and one public theorem. The source
and standalone Audit pass strict checks. Audit passes {jobs} jobs and checks
{deps} theorem dependencies. Public readback contains {public['theorem_signatures_and_axiom_checks']} complete blocks.
All 162 prior public blocks and 85 pinned prior source modules remain byte
exact. Only the three standard Lean axioms occur. FINDINGS retains every
Haskell repair handoff. Details: `lean/notes-current-traversal-coverage.md`.

'''
extra = f'''
### Traversal coverage and Haskell repair status

This checkpoint changes Lean proofs only. All previous Haskell fixes,
regressions and external repair instructions remain below without deletion.
The final successful fetch reads main at {upstream['main']}.
It remains an ancestor with the LPO and extraction documentation fixes.
KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated,
unbuilt and unexecuted. The positive-Int context-reversal finding remains
open. No Haskell source, Cabal file, native test or benchmark changed or ran.
Existing opaque Mu and Union behavior remains outside full expansion and
rendering coverage. This result does not establish a new Haskell defect.

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
note = f'''# Constructive coverage of ordered native child traversal

Source checkpoint: {head}.
Published base: {base}.
Main: {upstream['main']}. The final successful fetch confirms ancestry.
Previous note: `notes-current-incoming-coverage.md`.

## Target and current statement

The target remains correctness of the whole CFTA system. It includes exact
finite-tree transformations, enumeration soundness and coverage, API behavior
and physical Haskell correspondence. Preserve the optimized interned core,
older constructor and equality proofs, counterexamples, repairs and drafts.
The complete target remains open.

The new theorem is
SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_accepting
in SourcePruningEnumerationTraversalCoverage. It retains the complete
original TraversalResources admission, witnesses and result conjunction.
Its observer quantifies over an ambient environment, residual meaning,
original assignment and an ordered list of concrete terms. Original state
Satisfies and Language.All₂ relate the original inputs to these terms.
Each incoming native value accepts its term. EVERY original bucket entry
must hold under the original assignment, including duplicate entries.

The theorem constructs a final assignment that agrees below the original
counter and satisfies the original state at the original heap. The SAME
actual result completes with the SAME chosen fragments, caller, saved query
table and indexed cache. Filling those fragments gives exactly the input
term list, in order. The final state satisfies the constructed assignment
at the SAME actual final heap. All work bounds and runtime witnesses occur
before the semantic observer. A desired future assignment, successful
result or final Satisfies is not an input.

Original admission remains explicit: native Context with full Memos and
Inventory, Safe, recorded Roots, correct waiting counts, actual native
expandable flags, PendingRealized, genuine available closed inputs with
bounded pending bucket references, Fits, the original Reserved cost and
the source guard annotation Heap. No supplied traversal Ranges or new
semantic producer admission is added.

## Actual ordered composition

The proof follows the original resource induction. Each reached head invokes
the checked child accepting producer once, before any model is chosen.
The returned caller, indexed cache and FULL middle Memos supply the suffix.
Actual Post.effects.keeps retains availability. Growth and protected
enumerated slots derive the suffix bounds and pending admission. Original
prefix and after_prefix reservations supply the exact remaining cost.

The original result retains both successful traversals and stopped prefixes.
A rejected head retains its native effects and pads unused suffix resources
without executing the suffix. Under the accepted-model observer, child
coverage constructs an actual singleton. That singleton contradicts the
empty rejection list. Safe is not inferred from a rejected cache.

A successful head supplies a new assignment and its exact fragment filling.
Original bounds on every later sc.var and holds_extension transfer all later
bucket obligations. Native value acceptance has no heap parameter. The
suffix observer uses the actual middle-state satisfaction and constructs
its final assignment. Counter growth composes agreement on old variables.
state_assignment_congr retains every original forest equality, stored slot
restriction and residual fragment under this final assignment.

The head FragmentBound is at the MIDDLE counter. fill_bounded uses agreement
below that counter to retain the head filling after later allocations.
Using only the original counter would omit holes allocated by the head.
List.map_cons and the suffix filling equality retain the exact order.
Empty inputs keep the original assignment and complete immediately.

The old sum/max bounds combine the stable head and suffix runs. The final
packet keeps Post, full Memos, query equality, returned roots and indexes,
origins, all protection/reference families, pending history, fragment bounds,
complete-or-stopped shape, final Fits and the advanced guard carrier.
Query equality is used only for the runtime query argument. It does not
replace full memo equality. The final completion proof substitutes the
derived tail result throughout its dependent proof context.

## Verification and attempts

One module contains {stats['lines']} lines and {stats['bytes']} source bytes.
It declares one public theorem and no new definition, predicate or structure.
The exact installed source and standalone Audit pass strict checks with
-DwarningAsError=true and -Dlinter.all=true. All recorded compiler commands
run serially with measured 4 GiB memory.max/high and zero swap.

The complete Audit build includes the new module and passes {jobs} jobs.
It checks {deps} theorem dependencies. The earlier unused-input dependency
warning remains in the build log. The successful new source strict log is
empty. The Audit strict log records its checked theorem count.

Public output has {public['theorem_signatures_and_axiom_checks']} full signature and axiom blocks without elision.
All 162 prior blocks match byte exactly. The entire prior public output is
an exact prefix of the current output. All 85 pinned prior source modules
retain their published bytes. Audit adds one import; removing it recovers
the entire old file. Only propext, Classical.choice and Quot.sound occur.
There is no sorry, admit tactic, custom axiom, native_decide, heartbeat
increase or linter suppression. Public output is {public['bytes']} bytes, SHA256
{public['sha256']}.

The first source attempt failed only at the last completion rewrite. Its
dependent result match includes tail run, shape and observer proofs.
The final source replaces dsimp[result]; rw[tailComplete] with
subst tailResult; rfl at that proof step. The entire public statement is
byte identical. The initial source and its full 23630-byte error log remain.
Removing the appended observer and restoring the old theorem name recovers
the entire original 4287-byte proposition exactly. Preserve both attempts,
the exact delta, contract comparisons and source inspection records.

## Strongest global claims and remaining work

H6 retains exact accepted finite trees for its covered closed construction,
original guard allocation history and empty inherited payload. Any fixed
finite number of pruning rounds has an actual complete call trace with
sufficient mathematical width and fuel. Convergence and withoutRedundantEdges
remain outside that theorem.

run_initial_finite_render_sound retains finite enumeration soundness from
the literal native startup under its declared native Context, initial arity,
resource and policy contracts. Its own outputs must be Discharged, render
successfully and pass residual checks. Their rendered terms then belong to
the original root language. These global statements are unchanged here.

The new result closes ordered SYMBOLIC CHILD PREPARATION coverage.
Next derive local selected-edge execution from an accepted parent term:
successful actual guard projection, own and inherited arity, fresh equality
witnesses, accepted ordered child inputs and the final residual check.
Native guard acceptance must match the actual residual interpretation.
Do not infer an arbitrary residual predicate from native guard acceptance.
An existing helper requires valid inherited tries for a backward descent
law. A one-way path descent law may avoid that extra gate for coverage;
that proposed bridge remains unproved in this checkpoint.

Whole recursive coverage also needs a selector that retains an accepting
edge and pruning callbacks that retain an equivalent language. Current
subset and length laws admit edgesOf := fun _ => []. Stop and depth policies
can park or exhaust. Fresh Mu and Union still store empty buckets and can
remain parked. Chosen finite fillings alone do not establish full expansion,
Discharged or renderability. Preserve all earlier opaque-retention findings.

Complete public native Context, arity, physical/full memo and resource
admissions, remaining API obligations and physical Haskell correspondence.
No Haskell source or Cabal file changed. No native test or benchmark ran.
Main retains the LPO and extraction documentation fixes. KBO candidate
d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted. The positive-Int context-reversal finding remains open.
FINDINGS retains every previous Haskell repair handoff. The full goal stays
ACTIVE. No completion percentage or date is claimed.

## Restart evidence

Portable evidence: `restart-evidence/20261027-traversal-coverage/`.
The manifest records stored bytes. decoded-files.json records original
bytes for deterministic gzip payloads. Run verify-evidence.py with the
snapshot path. Use --committed after the evidence commit to compare every
payload with Git. Retain original sources, attempts, logs, public output,
contract comparisons, source cuts, reviews and all nine old document bodies.
Keep publication receipts outside the frozen TEMP area and archive.
Earlier frozen evidence remains unchanged.
'''
name = 'lean/notes-current-traversal-coverage.md'
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
