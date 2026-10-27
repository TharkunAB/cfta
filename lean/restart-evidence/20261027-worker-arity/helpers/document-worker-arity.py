from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-worker-arity-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
public = json.loads((area / 'public-validation.json').read_text())
assert public['status'] == 'pass'
assert json.loads((area / 'source-validation.json').read_text())['status'] == 'pass'
assert json.loads((area / 'final-upstream-refresh.json').read_text())['main_is_ancestor']

prefix = f'''
## Arity through actual local reduction and parent construction

Source checkpoint: {head}.
The actual local equality reduction now derives arity at its returned native
heap. The literal completed local worker derives the same result. The actual
parent-edge graph uses this result at its real reduction endpoint before it
constructs the parent. Both live and rejected parent branches retain the
invariant for every resident edge record. Each projected root-child reference
fits the actual child count. The proof keeps the complete original admission
and adds only a genuine initial arity-valid heap. It assumes no future child
arity, future successful query or desired final invariant.

The proof composes actual cold exposure, both gate families, projection,
required children, probe selection, merge, conjunction, seeded queries,
class scans, shared targets, class editing and the ordered class pass.
Caller begin/finish and checked-state advance retain their exact native
heaps. Checked raw rebuild uses the original resident key and actual child
count. Every phase retains its actual returned states and full memo caches.
The preceding all-outcome native-query theorem remains unchanged.

This is not yet an arity theorem for the whole recursive partial worker or
its entire finite history. The next task is to compose the actual worker
branches, captured-cache restores and history steps. Derive
ResourceHistoryWithArity at the SAME producer bound and actual own output.
Keep the entire original producer admission and result. The recursive
semantic theorem still requires its arity-certified history observer.
H6, enumeration coverage, API obligations and physical Haskell correspondence
retain their previous scopes. The whole-system goal stays ACTIVE.

Sixteen modules contain 2693 lines and 79 new public theorems. All pass strict
checks. Audit passes 4195 jobs and checks 79883 theorem dependencies. Full
public output has 91 signature and axiom blocks without elision. All 12 prior
strongest blocks match byte exactly. Only the three standard Lean axioms
occur. Selection adds one effect structure and one callback predicate.
No Haskell source changed. FINDINGS retains all repair handoffs. Details:
`lean/notes-current-worker-arity.md`.

'''

extra = '''
### Worker arity and Haskell repair status

This checkpoint changes Lean proofs only. Every previous Haskell repair,
regression and external repair handoff remains below without deletion.
The final successful refresh reads main at
8766699b594eaad80381af2eee034c378ccf3192. This commit is an ancestor of the
source checkpoint. The LPO fix and extraction documentation fixes remain
integrated. The separate KBO candidate
d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted here. Keep its prior source assessment. The positive-Int
context-reversal finding remains open in this branch. Run its exact native
regression after the repair reaches main.

The new arity proof closes the local-reduction intermediate-heap gap in
the actual parent-edge graph. It does not establish a new Haskell defect,
native regression success, whole recursive worker invariant or complete
implementation correspondence. Keep those claims separate. Existing
constructor, equality, field-pool and other Haskell findings remain intact.

'''

note = f'''# Arity through actual local reduction and parent construction

Source checkpoint: {head}.
Published base: {base}.
Imported main: 8766699b594eaad80381af2eee034c378ccf3192.
The final fetch succeeds and confirms that main is an ancestor.
The whole CFTA formalization goal stays ACTIVE. Preserve the optimized
interned core, older constructor and equality proofs, marked drafts,
counterexamples and repairs. Previous note:
`notes-current-native-prefix-arity.md`.

## Target and strongest semantic statements

The target remains correctness of the whole CFTA system. It includes exact
finite-tree transformation laws, enumeration soundness and coverage under
explicit solver, selector and pruning contracts, and physical Haskell
correspondence. This target remains incomplete.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, remains the
strongest global exact finite-tree construction theorem. A covered closed
construction, original guard-allocation history and empty inherited payload
derive one actual finite call trace for any chosen finite number of rounds.
The theorem supplies sufficient mathematical width and fuel bounds. Every
actual node call completes. The final value accepts exactly the original
finite trees at every ambient environment. It does not assert convergence
or include withoutRedundantEdges. It does not verify all Haskell execution.

The recursive semantic theorem retains its original full contract. An actual
arity-certified ResourceHistory, actual restart decision, initial Canonical,
own-output Discharged, successful native rendering, checked returned
residuals and original stored-root lookup construct an assignment. The term
belongs to the original native value and satisfies every original suspended
Holds clause. The assignment satisfies the original input, own output and
rendered state. Desired original acceptance and final Satisfies are not
inputs. The finite producer retains its complete admission and result.
Arity certification remains an observer antecedent.

The previous all-outcome native query theorem remains unchanged. Initial
physical Good, genuine initial ArityOrigins.Heap and actual InputsThrough
derive Heap at EVERY finite native node or edge query outcome. Yielded,
done, failed, constraintError and blocked states are covered. This statement
applies to those actual native queries. It does not cover every failed or
stopped prefix of the full local or recursive worker.

## New composed invariant

SourcePruningEnumerationLocalReductionArity.reduction_heap retains the
complete admission of SourceCurrentAllocatedLocalReductionActual.verified.
It adds only Heap at the initial native heap. The proof derives Heap at the
actual returned checked state. literal_heap uses the literal completed local
worker result and its original soundness admission to obtain the real reads.
It then applies reduction_heap. No new success trace is assumed.

SourcePruningEnumerationParentArity.parent_heap retains the complete
SourceCurrentAllocatedParentEdgeActual.verified admission plus initial Heap.
The rejected case uses the real sentinel constructor. The live case uses
the SAME actual local-reduction reads to derive the real middle Heap.
Existing physical effects supply loaded-field readiness at that middle.
The final checked constructor retains arity. Equality of the full actual
constructor result aligns both the returned value and checked state.
The proof does not apply a constructor theorem to the earlier input heap.

Heap checks every canonical edge-record key at its actual number of
children. Fits says that every successful constraint projection references
only existing root children. The invariant includes records created by
recursive child calls, cold stored substitution and leaf queries.
Constraints that cannot project keep the existing conditional Fits meaning.
The proof does not strengthen that meaning without a projection witness.

Initial SemanticReady, costs, inventory, values, original guard allocation,
required domains, correct emptiness memo, stored merge memo, cache coverage,
full global memo validity and finite-range assumptions remain where the
original interfaces require them. Initial Heap must come from real checked
origins. Raw buildEdges, normalized fields, closure and memo validity alone
do not replace that input. The new theorems do not accept desired final Heap,
final acceptance, final Satisfies or arbitrary future preservation laws.

## Actual phase composition

GateArity treats the primary and secondary physical trace families. It
retains semantic readiness, cache growth, costs and arity after each actual
node, child, edge-list, path and class read. Stored unfolding uses its
checked origin theorem. ProbeExposureArity proves the actual cold collector
and nodeEdges outcomes from initial facts, availability and Heap. Its result
also covers pending, unresolved and exhausted collector outcomes.

ProjectionArity follows real ordered head reads, union, recursive project,
rows and forest construction. RequiredArity follows the actual mutual node,
children and row workers, then requireAll. A reconstructed edge uses the
original resident key and the actual child-count equality. Physical
coherence and initial Heap derive Fits for the copied guard.

SelectionArity combines the original keeps, semantic and cost effects with
arity transport. Its comparison callbacks use actual cold exposure.
MergeArity discharges checks for every actual Run constructor. Small groups
preserve copied child counts. Large groups use their real Top guard.
Allocated merge retains its literal erasure and actual operation allocation.
SharedTargetArity follows actual projection, merge and native query before
the real shared leaf receipt. Initial original-value availability remains an
explicit old producer input. No final leaf resource observer is assumed.

ConjunctionArity follows actual exposures, projections, required paths,
tuples, allocated rows and memo hit/miss decisions. SeededArity follows the
actual first operand and ordered right fold. ScanArity handles selected,
skipped, continued and stopped class-scan branches. Each phase derives its
intermediate physical readiness from existing verified effects. It derives
arity from the new phase theorem, not from physical growth alone.

ClassEditArity follows the actual mutually recursive ordered reads and
shared leaf. ClassPassArity retains that namespace and proves the actual
class read, tail-before-head fold and final pass. LocalReductionArity then
splits unchanged, empty-child and real class continuations. The completed
continuation uses the literal scan, requireAll and class-pass endpoints and
their exact intervening full memo caches. A stopped scan needs no suffix.

CallerArity retains literal heaps through begin, finish and actual checked
state advance. RawRebuildArity uses a resident original record, coherence
and equal actual child counts. These are primitive results. They do not yet
compose every recursive worker call or captured-cache history step.

## Validation and retained attempts

Sixteen modules contain 2693 lines and 79 new public theorems. Each passes
-DwarningAsError=true -Dlinter.all=true. Audit passes 4195 jobs and checks
79883 theorem dependencies. Standalone strict Audit also passes. Public
output has 91 complete signature and axiom blocks: 79 new and 12 prior
strongest declarations. All 12 prior blocks match byte exactly. Their 18
source modules also retain the exact published bytes. Selection adds one
Effect structure and one Callback predicate definition. Export aliases do
not count as new definitions. Public output contains no elision.

Only propext, Classical.choice and Quot.sound occur. The proofs add no sorry,
admit tactic, custom axiom, native_decide, heartbeat increase or linter
suppression. The existing worklist constructor is named admit; its actual
induction case is not an admit tactic. The source validator distinguishes
that exact case. Strict checking and full axiom readback also verify it.

All heavy checks run serially with memory.max/high4GiB and swap0. Builds
replay the existing unused-input warning in
InternedFreshOrdinaryClosedCompletion. Each new module has an empty strict
raw log. No Haskell or Cabal source changed. No native Haskell build is
claimed for these Lean proof changes.

Retain every attempted source and actual raw log. Exposure v1 fails on an
eliminated binder. Projection v1/v2 fail on quoted notation and constructor
endpoint elaboration. Required v1 fails on quoted notation. Selection v1
fails on four missing field documents. Conjunction v1 fails on a namespace
alias. Seeded v1/v2 fail on binder arguments, a reserved identifier and unused
instance scope. Merge v1 fails on dependent output elimination. ClassEdit's
first tested version v3 fails on two literal endpoint reductions. Local
reduction v1 uses a nonexistent receipt.available field; v2 uses its real
receipt.resident field. These local repairs preserve the public contracts.
Untested draft variants remain marked as untested. Failed checks do not
count as proof validation. Parent, ClassPass, gates, raw rebuild, caller and
scan pass their first strict checks.

Evidence area: /tmp/mcfta-worker-arity-20261027.
Portable archive: restart-evidence/20261027-worker-arity.
The archive retains exact sources, tested and untested variants, actual raw
logs, full public output, literal review cuts and document inverses.
The verifier checks exact payloads, compressed originals, review seals,
installed sources and preserved old document bytes. After the evidence
commit, use --committed to check tracked bytes. Freeze the evidence area
and archive once. Save publication receipts outside both.

## Remaining proof work and Haskell handoff

Compose the actual general PartialWorker branches with the new phase
theorems. Follow the literal returned checked states, optional binders,
reconstruction, caller caches, captured-cache restores and descendants.
Derive arity for each actual finite-history step from genuine initial
origins. Then construct ResourceHistoryWithArity at the SAME finite producer
bound and own-output state. Keep every original admission and result field.
Do not add future child arity or future whole-history certification as a
producer premise. Do not weaken the recursive semantic statement.

Enumeration coverage, remaining API contracts and physical Haskell
correspondence remain separate open targets. The full goal stays ACTIVE.
No completion date or whole-system completion percentage is established.

FINDINGS retains all previous fixes, regressions and external repair
handoffs without deletion. The LPO fix and extraction documentation fixes
remain integrated. Main remains 8766699b594eaad80381af2eee034c378ccf3192.
The separate KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains
unintegrated, unbuilt and unexecuted here. Its prior source assessment is
unchanged. The positive-Int context-reversal finding remains open. Run its
exact native regression after that repair reaches main. This checkpoint
establishes no new Haskell defect or native regression success.
'''

paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in paths:
    target = root / name
    previous = target.read_bytes()
    assert previous == subprocess.check_output(['git', 'show', base + ':' + name], cwd=root)
    saved = area / 'prior-documents' / name
    saved.parent.mkdir(parents=True, exist_ok=True)
    saved.write_bytes(previous)
    first, rest = previous.split(b'\n', 1)
    insertion = (prefix + (extra if name == 'FINDINGS.md' else '')).encode()
    current = first + b'\n' + insertion + rest
    target.write_bytes(current)
    records.append(dict(path=name, bytes=len(current), sha256=hashlib.sha256(current).hexdigest(),
        offset=len(first) + 1, inserted_bytes=len(insertion)))
name = 'lean/notes-current-worker-arity.md'
assert not (root / name).exists()
current = note.encode()
(root / name).write_bytes(current)
records.append(dict(path=name, bytes=len(current), sha256=hashlib.sha256(current).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(paths + [name], indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(records), note_bytes=len(current))))
