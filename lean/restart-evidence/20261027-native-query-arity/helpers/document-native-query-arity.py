from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-query-arity-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
assert json.loads((area / 'public-validation.json').read_text())['status'] == 'pass'
prefix = f'''
## Arity through complete native queries and returned memo cells

Source checkpoint: {head}.
Initial physical Good, an arity-valid edge-record heap and the SAME actual
completed rich native query trace now derive arity of the ENTIRE returned
edge-record heap. Both node and edge queries retain every old record and
check every child-created record. Strong induction on actual trace length
discharges both recursive call families. No per-child arity, future successful
answer, semantic completion law or certified-origin trace is added as a premise.
Every completed edge memo cell after a node query derives arity from its actual
resident record and final physical coherence. Warm hits retain the heap.

The proof reuses actual rich trace splitting. It derives intermediate physical
Good and fields. Actual child walks retain their exact lengths and full caches.
Node compilation derives its local constructor condition from its real code.
The accepted edge prefix checks the new key after actual child calls. The
sentinel checks its real Top/Empty constructor. Optional binding also retains
arity at its actual completed or pending constructor outcome.

The whole-query result requires an actual completed rich trace. It does not
cover every stopped, failed or blocked query prefix. Such prefixes, actual
local reduction, cold exposure, narrowing, captured-cache restores and the
finite-history producer still need resource composition. The previous
whole-history acceptance observer keeps its arity-certified history premise.
H6 and all six previous strongest full contracts stay unchanged. Enumeration
coverage, remaining API contracts and physical Haskell correspondence remain
open. The whole-system goal stays ACTIVE with its original full scope.

Six modules, 937 lines, 22 public theorems and one WorkFits definition pass
strict checks. Audit passes 4173 jobs and 79689 dependency checks. Public
readback contains 28 full signatures and axiom sets with no elision. The six
old strongest blocks match byte exactly. No Haskell source changed. FINDINGS
retains all fixes and repair handoffs. Details: `lean/notes-current-native-query-arity.md`.

'''
extra = '''
### Native query resource and Haskell repair status

This is a Lean invariant result. No Haskell source or Cabal file changed.
All previous fixes, runnable regressions and repair handoffs remain below.
Main was 8766699b594eaad80381af2eee034c378ccf3192 at the successful refresh.
The separate KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d is not
integrated, built or executed here. Its prior source assessment remains the
only assessment. The positive-Int context-reversal finding remains open in
this branch. Run its exact native regression after the repair reaches main.

The completed-query proof now checks every child-created edge record and
derives arity for completed physical edge memo cells through residency. It
does not infer arity from NodeGood, EdgeGood or a generic Post alone. Actual
Inputs and initial physical Good stay in the rich trace contract. It does
not turn arbitrary raw done into such a trace. General raw buildEdges still
needs genuine original source checks or actual checked construction origins.
Every-prefix native preservation and full local-reduction/history composition
remain formalization work. No new Haskell defect follows from this boundary.

'''
note = f'''# Arity of complete native queries and their actual returned heaps

Source checkpoint: {head}.
Published base: {base}.
Imported main at refresh: 8766699b594eaad80381af2eee034c378ccf3192.
The full CFTA formalization goal stays ACTIVE. Keep the optimized interned
core and all older constructor/equality proofs, drafts, counterexamples and
repairs. Previous note: `notes-current-checked-arity-origins.md`.

## Target and strongest current claims

The target remains correctness of the whole CFTA system. It includes exact
finite-tree transformation laws, enumeration soundness and coverage under
explicit solver, selector and pruning contracts, and physical Haskell
correspondence. The target is incomplete.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, remains the
strongest global exact finite-tree construction theorem. Its covered closed
construction, original guard-allocation and empty inherited-payload contracts
remain unchanged. It derives finite call completion and exact original
finite-tree acceptance at every ambient environment. It does not establish
convergence or full Haskell execution correctness.

The strongest recursive semantic theorem also remains unchanged. An actual
arity-certified ResourceHistory, actual restart decision, initial Canonical,
own-output Discharged, successful native rendering, checked returned residuals
and original stored-root lookup construct an assignment. The term belongs to
the original native value and satisfies all original suspended Holds clauses.
The assignment satisfies the original input, own output and rendered state.
No desired original acceptance or final Satisfies is an input. The finite
producer keeps its entire original admission and result. Arity certification
remains an observer antecedent. This checkpoint does not remove it.

The new whole-query theorem is a resource result. Initial physical Good and
SourcePruningEnumerationArityOrigins.Heap, plus the SAME actual completed rich
node or edge query Trace, imply Heap at its complete actual returned state.
Heap checks EVERY edgeRecords key against that key's own child count. The
result includes all records created by recursive children. It assumes no
per-child arity result, final Heap or new future-success contract.

The trace retains actual physical Inputs at every yielded instruction. Good
contains physical memo validity, heap readiness, operation validity and loaded
normalized fields. It contains no desired arity result. Completion is observed,
not proved by this resource theorem. Bare execute=done is not promoted to a
rich trace. No new semantic result or source-language acceptance is assumed.

## Actual recursive proof

SourcePruningEnumerationNativeQueryArity.node_query_heap and edge_query_heap
use strong induction on actual yielded trace length. A request consumes one
step before its body. The actual rich bind inverse exposes a shorter body
and its real captured finish frame. Every nested call in that body has length
at most the body length, hence strictly less than the outer request length.
The induction therefore discharges both node and edge call families.

Warm hits keep the literal constructor heap. Missing or busy demands cannot
form the observed completed rich trace. Actual finish instructions change
memo cells but keep constructor records. The proof retains the actual original
request returned by demand and the complete intermediate checked state.

The compiler proof derives a private LocalWorks condition from literal
compileNode code. Its local Work instructions normalize nodes and unions.
They emit no edge-key requests. The condition covers all source branch
selectors, Mu entry, references, ordered union calls and joined row calls.
It is an internal proved fact, not a new public admission. Generic arbitrary
Code may still create an unchecked edge. No such universal claim is made.

The shared walk_heap lemma consumes only actual rich child traces and their
bounded call induction hypotheses. Existing physical effects derive Good at
each actual child endpoint. It retains the ordered returned values, operation
cache and both memo families. It does not assume arity for arbitrary lists.

The checked edge-body observer derives its accepted or sentinel branch from
its actual first instruction. Accepted execution exposes the original loads,
real ready check, updated operation state, rich ordered child Walk and actual
constructor endpoint. Its exact count is childFuel+2. Actual Walk length
matches the original checked incoming arity. ready_fits checks the new key.
The recursive induction checks every record created before that constructor.
The rejected branch checks the actual Top guard and one Empty child.

The primitive WorkFits condition follows only actual Work instruction results
and caches. It checks each current edge key, not arbitrary continuation values.
Actual optional binding uses checked stored encoding and reconstruction. It
retains Heap for complete and pending constructor outcomes. This local pending
lemma does not claim preservation for every pending whole query.

## Memo results and original input connection

node_query_edge_memo_fits checks EVERY completed edge memo cell at the actual
returned node-query state. Existing rich trace effects derive final physical
Good. Its edge memo validity supplies actual residency. Final coherence and
the derived entire Heap give guard arity at that resident payload's real child
count. No new arity field is assumed in NodeGood or EdgeGood.

The previous SourceChecked construction bridge can supply the initial Heap.
It records normalized original fields and actual accepted source checks at
original syntactic child counts. Checked source construction and stored
substitution/reconstruction already preserve it. General raw buildEdges still
does not check arity. Closure, Packet, normalized fields and residency alone
do not supply the initial relation. Keep genuine checked origins explicit.

## Remaining work

1. Extend the actual query resource to all reached stopping endpoints needed
   by enumeration, including stopped, blocked and failed prefixes. Keep the
   actual compiled program and captured finish frames. Do not assume arity
   for arbitrary generic Code or arbitrary continuation outputs.
2. Compose the resource through actual local reduction, cold exposure,
   narrowing, callbacks, cache restores and completed head advances. Existing
   reconstruction and constructor lemmas cover their own operations. They do
   not yet cover the whole worker schedule. A Parent live constructor starts
   at a middle state after reduction; its original-before to middle Heap
   still needs that actual reduction proof.
3. Keep the original finite-history producer admission and result. Derive
   ResourceHistoryWithArity at the SAME bound and actual own-output caches
   from genuine checked initial origins. Preserve inventories, full Memos,
   metadata, callback inputs and captured cache restores. Do not replace this
   task with a renamed per-history arity antecedent or final Satisfies premise.
4. Instantiate the unchanged whole-history rendering theorem with the derived
   certificate. Prove enumeration coverage separately under the actual solver,
   selector, pruning and recursion contracts. Keep all original proof targets.
5. Close API and physical Haskell representation gaps, including the direct
   union-find parent/member representation. This remains a whole-system goal.

## Validation and unsuccessful attempts

Six installed modules contain 937 lines, 22 public theorems and one WorkFits
definition. All six pass -DwarningAsError=true -Dlinter.all=true. Aggregate
Audit passes 4173 jobs and 79689 theorem dependency checks. Standalone strict
Audit passes. Full public output has 28 complete signature/axiom blocks and
the WorkFits definition, without elision. Only propext, Classical.choice and
Quot.sound occur. All six prior strongest blocks match byte exactly, and their
source files remain unchanged. All earlier source contracts remain intact.

All heavy checks run serially with memory.max/high4GiB and swap0. The aggregate
replays the pre-existing unused-input warning in
InternedFreshOrdinaryClosedCompletion. No new linter is suppressed. No sorry,
admit, custom axiom, native_decide or heartbeat override is introduced.

Preserve all actual failed attempts and source variants. The primitive draft
passes first strict checking. The request-frame draft first failed on an unused
instance scope and two implicit finish-state arguments. Explicit actual middle
states and a narrower instance scope pass. Rich body readback first failed on
nested record layout and a different inferred guard decision instance. The
correct layout and the same original guard instance pass. The standalone rich
walk passes first checking. The full node compiler draft first failed on a
grouped-pattern parser error, ambiguous unsupported names, instance scope and
an implicit optional-binder middle state. The corrected draft passes with the
same public contract. Whole edge-body Heap and full mutual query proofs pass
on their first attempts. All failed raw outputs are retained as failures.

Evidence area: /tmp/mcfta-native-query-arity-20261027.
Portable archive: restart-evidence/20261027-native-query-arity.
Use the archived verifier for exact payloads, compressed originals, source/cut
identities, review seals and document inverses. After commit use --committed
for exact tracked bytes. Freeze the area and archive after review and checks.
Save publication receipts outside them. Never edit earlier frozen bundles.

## Haskell status

No Haskell or Cabal file changed. Native tests were not repeated for these
Lean-only changes. FINDINGS preserves all fixes, regressions and external
repair handoffs. The LPO and extraction documentation fixes remain integrated.
Main was 8766699b594eaad80381af2eee034c378ccf3192 at refresh. Separate KBO
candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated,
unbuilt and unexecuted here. Its prior source assessment is retained. The
positive-Int context-reversal finding remains open in this branch. Run the
exact native regression after the repair reaches main. No new Haskell defect
or runtime success follows from this Lean resource proof.
'''
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in paths:
    path = root / name
    previous = path.read_bytes()
    assert previous == subprocess.check_output(['git', 'show', base + ':' + name], cwd=root)
    stored = area / 'prior-documents' / name
    stored.parent.mkdir(parents=True, exist_ok=True)
    stored.write_bytes(previous)
    first, rest = previous.split(b'\n', 1)
    insertion = (prefix + (extra if name == 'FINDINGS.md' else '')).encode()
    current = first + b'\n' + insertion + rest
    path.write_bytes(current)
    records.append(dict(path=name, bytes=len(current), sha256=hashlib.sha256(current).hexdigest(),
        offset=len(first)+1, inserted_bytes=len(insertion)))
name = 'lean/notes-current-native-query-arity.md'
assert not (root / name).exists()
current = note.encode()
(root / name).write_bytes(current)
records.append(dict(path=name, bytes=len(current), sha256=hashlib.sha256(current).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(paths + [name], indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(records), note_bytes=len(current))))
