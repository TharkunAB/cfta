# Independent current class-worker review

Reviewed the current ClassWorker, Completion, Stability, and Actual modules.
Also read SharedEditWorkerActual at the dependency boundary. No material
defect was found. No proof source was edited or rebuilt by this review.
The source hashes are in `class-review-SHA256SUMS`.

## Source schedule and retained state

`runClass` captures its supplied input forest and starts only its class-local
slots empty. Its checked state and warm merge memo are the supplied values.
It executes the actual compiled edit list. A failed edit returns the exact
Fault and full reached SharedState, including slots and the returned merge
memo. Outcome accessors project checked state and memo. They do not replace
the full failed outcome. Bind skips its continuation on failure.

The class fold executes the tail before it invokes the head. The head
captures the tail's literal returned forest, checked state, and merge memo.
This matches `foldr reduceEClass withNeededChildren eclasses` at
`cfta/src/Data/CFTA/Equality/Operations.hs:211`. Each class starts separate
local target slots. No native table, domain cache, equality-operation table,
or completed merge memo is reset. Final propagation runs only after the
whole fold succeeds. It changes no cache. A failed tail skips both the head
class and final propagation. Empty class lists still run propagation.

Completion derives six stable bounds from each finite compiled class,
right fold, or propagated pass graph. It follows the actual graph states.
No completed callback implements an executable branch. The separate
success-stability proofs need no physical or semantic premise. They compare
two successful executions at maximum bounds and retain the whole return.

## Actual return, inventory, and language

Actual.finite constructs a graph, reads, computed next inventory, probes,
and physical and semantic receipt from legitimate initial facts. Its reached
range plan contains machine checks at actual graph prefixes. It contains
no output law or future body-success condition. Actual.verified constructs
this receipt independently, then uses unconditional pass success uniqueness
to identify its ordered forest, complete checked state, and saved merge memo
with the supplied execution. These proved equalities justify substitution.
It does not select an unrelated existential return as the worker result.

The caller endpoints retain the computed next inventory's At proof at the
same returned checked state. PartialState.advance keeps the complete outer
node and edge result families and the literal old fourth memo. Actual
physical Effects preserve the old cell laws and fourth correctness. The
saved merge memo is the actual pass return. ProbeHeap follows the reads
for that returned graph. No final invariant or result language is an input.

The legitimate initial Context remains explicit. It includes warm native
admission, outer-cell soundness, stored and covered merge entries, fourth
correctness, global coherence, and probes. Selected path domains, coherent
nontrivial class records, source-resident input values, and reached ranges
also remain explicit. These are not a proof for arbitrary warm caches.
Unrelated original siblings need no whole-forest closedness premise.

The result always narrows the original forest. Its language equals that
forest only under satisfaction of every selected original class. Individual
target merging has an inclusion law, so an unconditional target or pass
language equality would overstate the result. The public signatures retain
the required ClassSat condition.

SharedEditWorkerActual uses the same route for node, child, and list returns.
Its concrete success-uniqueness endpoints have no callback premise. The
language theorem composes the independent edit-language proof after it has
obtained the aligned graph. No own-parent language law is assumed.

The returned Reads are logical witnesses for a graph at these exact
endpoints. Successful execution uniqueness identifies the output and full
state; it is not a theorem of host global-event trace identity. The modules
state that they do not execute concrete host global tables. GHC forcing,
lazy publication, native containers and identity lifetime, the remaining
outer executable ports, and general constrained outer termination remain
separate. No new Haskell defect or repair was found.

## Imported public validation

The root reported canonical Actual-batch success with 1324 jobs. This review
ran only the following direct command against its canonical interfaces:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-edit-worker/class-review-public.lean
```

`class-review-public-1.log` returned exit 0 with no warnings. Four public
axiom checks and complete signatures cover finite, verified, caller, and
caller_finite. Dependencies use only propext, Classical.choice, and
Quot.sound. Three external kernels pass:

- Two coherent nontrivial classes construct six executable bounds and an
  actual pass return. The same Post retains both outer result tables and
  old-fourth correctness. Both ClassSat assumptions derive language iff.
- An actual failed tail edit retains its full SharedState through the fold
  and pass. The head and propagation do not execute.
- An empty class list with an Empty input still propagates Empty through
  all input positions at zero bounds and retains checked state and memo.

No canonical process or source mutation belongs to this review. No owned
process remains.
