from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-recursive-meaning-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
aggregate = (area / 'build-aggregate-final/raw.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', aggregate).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', aggregate).group(1)
public = json.loads((area / 'public-validation.json').read_text())
assert public['status'] == 'pass'

prefix = f'''
## Actual flat captured rendering now restores original captured acceptance

Source checkpoint: {head}.
Six new modules prove captured-step and prefix-operation language results.
Original captured admission derives a uniform sufficient bound before the
related flat input. An actual completed flat receipt at that bound supplies
its own reached heap, safe ordered earlier cache and backward language law.
Discharge, actual flat rendering and checked residuals construct an assignment
and derive acceptance at the original captured edge and parent node.
No old successful render, future completed family or assignment is an input.
Canonical, numeric Ranges, nonterminal, fresh arity and retention stay explicit.

Actual native narrowing returns exactly its accepted filtered exposed edges.
Every accepted result term belongs to the original independent node language.
An actual recursion check preserves assignments when it does not repeat.
A repeated check clears only its bucket and retains the native handle.
Its original assignment holds iff the reached assignment holds and every
cleared suspended constraint holds. The same exact law holds for flat checks.
An ancestry key alone does not establish those suspended constraints.

Actual stable complete child traversal now has the full existing semantic
iff and ordered effective-bucket relation from original finite resources.
The proof derives each reached leaf Ranges. It does not assume universal
traversal Ranges or assert validity of every low-fuel prefix.
Next lift this resource language result through selected and captured edges.
Then compose actual recursive histories and recover parked constraints.
Original recursive-input acceptance and enumeration coverage remain open.

Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
All six modules and Audit pass strict checking. H6 stays unchanged.
No Haskell source changed. FINDINGS preserves every earlier repair handoff.
Details: `lean/notes-current-recursive-meaning.md`. The full goal stays ACTIVE.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in documents:
    path = root / name
    old = path.read_bytes()
    assert old == subprocess.check_output(['git', 'show', base + ':' + name], cwd=root)
    target = area / 'prior-documents' / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(old)
    first, rest = old.split(b'\n', 1)
    data = first + b'\n' + prefix.encode() + rest
    path.write_bytes(data)
    records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
        offset=len(first) + 1, inserted_bytes=len(prefix.encode())))

note = f'''# Captured acceptance and actual prefix assignment meaning

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The formalize pull and main fetch succeeded. Main did not change.
The preceding goal turn made verified progress and pushed fc29f046e.
Its note is notes-current-recursive-outputs.md. The full goal stays ACTIVE.
Preserve the optimized interned core and all earlier proofs, repairs,
counterexamples, uncompiled proposals and marked drafts.

## Target and strongest current claims

The target remains whole-system source-connected correctness. It includes
exact finite-tree language preservation and enumeration soundness and coverage
under explicit solver and pruning contracts. This checkpoint does not close it.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
global exact finite-tree language result. Covered closed construction and a
valid original guard-allocation history derive the mathematical width and fuels
for each finite budget and round count. Actual formal calls complete. The final
node remains available and has exactly the original accepted finite trees in
every ambient environment. Its inherited payload is empty.

The preceding recursive theorem still supplies finite-depth actual flat
execution, the same stable earlier result, its entire OutcomeResources and
certificates for every emitted output, including output prefixes before stops.
Output-origin classification holds at all finite fuels. Done still does not
imply Discharged. Native recursive boundaries can remain pending.

The new captured rendering result proves original captured acceptance for an
ACTUAL flat completed captured receipt at a derived sufficient bound. It uses
the SAME completed cache and actual reached heap for rendering and assignment
construction. It does not apply that assignment directly to a later recursive
descendant cache. Backward history between those endpoints remains necessary.

## Actual flat captured completion and rendering

SourceFlatPruningCapturedEdge.complete_sound_current uses the original
captured completion producer once. That producer fixes its stable earlier
result and independent bounds before any related flat input is supplied.
The sum of those bounds gives one sufficient diagonal work bound.

At any larger bound, an actual flat complete receipt identifies the earlier
complete result. The fragment, Caller and Queries are equal. The recovered
flat cache relates to that exact earlier cache. A stopped canonical result
contradicts the actual flat complete observation. No successful earlier
completion family is assumed by the public theorem.

The earlier completed packet supplies Safe and dependency-order transport.
The existing stable captured soundness theorem restores the earlier input
assignment and proves edge meaning, parent meaning, suspended constraints and
the captured fragment equation. related_satisfies transports both endpoints.
The native languages use each literal endpoint heap.

SourceFlatPruningCapturedEdge.render_sound_current then constructs the
assignment from explicit Discharged, ACTUAL flat rendering and checks of every
actual returned residual. It derives acceptance of the rendered term by the
original captured edge and parent. It retains the original flat assignment,
the completed and rendered assignments, the fragment equation and exact
unchanged rendered core. It assumes no desired assignment or old render.

Both results retain the genuine original Context and cache admission. They
also retain Canonical, numeric selected-edge Ranges, nonterminal inherited
bucket, fresh projected arity and child-retention gates. The bound guarantees
the correspondence needed to interpret an actual completed receipt. It does
not guarantee that every admitted edge returns complete rather than stopped.
The underlying completion producer retains its full original completion packet.

## Exact meaning of native narrowing and recursion checks

SourcePruningNativeMeaning reads the actual narrowing observation. Its
narrowAt_edges theorem retains the literal exposure and node-construction
equations. The result accepts exactly the filtered exposed edges with their
full symbols, guards and ordered child languages. narrowAt_sound combines
that result with the independent guarded reader soundness theorem. Arbitrary
filter decisions preserve this direction of language inclusion.

SourcePruningOuterNarrow.narrow_sound includes the actual Mu and typed skips.
It covers the actual filtering route at its own input heap. Independent
guarded probes are a genuine premise of native reader soundness. A current
Context supplies them through initial.ready.semantic.guarded. The raw Ready
comes from initial.ready.semantic.ready. Context.probes has a different probe
invariant and must not be substituted for the independent language premise.
This soundness result does not establish pruning coverage.

SourcePruningEnumerationParkedLanguage proves an exact assignment equivalence
for a real stored-bucket clear and for an ACTUAL repeated recursion check.
The native option/domain stays present. The original assignment is equivalent
to the reached assignment AND every removed Suspended.Holds constraint at the
same selected variable. A nonrepeated check preserves all assignments.

SourceFlatPruningRecursionMeaning proves the same law for an ACTUAL flat
successful check. The ordered result relation derives a sufficient earlier
check bound and supplies that success's related earlier endpoint. The theorem
requires the genuine earlier Ready and stored bucket. It assumes no future
successful execution. A repeated ancestry key is operational data. No current
theorem recovers the cleared constraints from that key alone.

## Traversal language from original finite resources

SourcePruningEnumerationTraversalCompletion.stable_complete_semantics_resources
replaces universal traversal Ranges with original Fits, a finite Reserved
certificate for cost inputs and the original guard carrier Heap. It retains
all earlier genuine inputs and the actual stable complete traversal family.
It retains the ENTIRE earlier semantic conclusion: a full assignment iff with
arbitrary residualMeaning and the ordered All2 effective child restrictions.
The literal retained conclusion has 1054 bytes and SHA256
6cdaf0da645b26525c5a9e558a5d3ae7164c9d22b5e828f452e62b567f3d1815.

The induction calls the canonical child resource producer at each head.
It derives that concrete leaf's initial_ranges from current admission.
The actual returned Post, full Memos, Safe/cache facts, Fits and guard carrier
feed the suffix. The original reservation splits at bucket.length + 1.
Repeated costs remain present. Origin and Protected retain incoming references.
Common sufficient bounds identify the supplied actual stable complete suffix.
Canonical rejection contradicts the supplied complete family at those bounds.

The result does not prove universal Traversal.Ranges. That predicate quantifies
over arbitrary successful child prefixes at every fuel. The proof also keeps
the source's effective-bucket semantics. It does not assert that a discarded
nonterminal bucket holds. Full-edge language soundness still needs its genuine
retention and projected-arity conditions.

## Verification, preservation and remaining work

Six modules contain 773 lines and 10 public theorems. Audit adds only six
imports. All six modules and Audit pass Lean 4.34.1 with warningAsError and
linter.all. Every new module has empty strict compiler output. Aggregate Audit
passes {jobs} jobs and {dependencies} theorem dependency checks. Its earlier
InternedFreshOrdinaryClosedCompletion unused-input warning remains recorded.

Installed readback covers 12 full theorem signatures and axiom lists. It
includes unchanged H6 and the earlier captured-rendering theorem. Only propext,
Classical.choice and Quot.sound occur. No sorry, admit, native_decide, new axiom,
heartbeat increase or elision was added. Readback has {public['bytes']} bytes.
SHA256: {public['sha256']}.
Every heavy check runs serially with memory.max/high=4294967296 and swap=0.

Initial failed parking inputs retain actual elaboration and strict diagnostics.
Fixes made state substitutions explicit, used the qualified state-read lemma,
restored the local List monad instance and corrected exact simplification.
The native draft needed two elaboration fixes: the already reduced exposure
equation uses rfl, and namespace opens are separate commands. The traversal
proposal passed its first strict check without source changes. Every proposal,
revision, source snapshot, focused cut, review and actual check remains in
restart-evidence/20261027-recursive-meaning.

Every earlier proof source is unchanged. H6 and the older captured-rendering
theorem retain their checked identities. Every historical document byte is
preserved below the new status regions. No Haskell source changed. FINDINGS
retains all repair handoffs for external work and extraction progress limits.
No new Haskell repair follows from the parking characterization. Native tests
were not rerun for these Lean-only additions.

Next lift resource-based traversal semantics through the selected-edge
neutral-language and captured-finalization proofs. Use the full resource
producer endpoints instead of assuming universal low-fuel Ranges. Then compose
actual selected prefixes, callbacks and recursive branches backward. Recover
cleared suspended constraints from a genuine semantic ancestry/history law,
or prove why the relevant completed finite output excludes that branch.

Derive initial Canonical, projected arity and retention histories where needed.
State pruning coverage contracts. Prove original recursive-root acceptance and
enumeration coverage. Discharge/render existence, recursive boundary treatment,
complete search depth, unbounded convergence, physical Haskell containers,
concrete solver behavior, machine bounds and practical resource limits remain
separate obligations. Do not mark the full goal complete.
'''
# Read the exact retained-conclusion identity from its verified comparison.
comparison = json.loads((area / 'traversal-conclusion-comparison.json').read_text())
note = note.replace('6cdaf0da645b26525c5a9e558a5d3ae7164c9d22b5e828f452e62b567f3d1815', comparison['conclusion_sha256'])
name = 'lean/notes-current-recursive-meaning.md'
data = note.encode()
(root / name).write_bytes(data)
documents.append(name)
records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(documents, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'documents': len(documents), 'note_bytes': len(data), 'note_sha256': hashlib.sha256(data).hexdigest()}))
