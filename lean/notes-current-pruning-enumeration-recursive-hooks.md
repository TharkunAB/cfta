# Concrete recursive pruning continuations

Callback exactness: `231b4a5ae`.
Selected-prefix separation and legacy equivalence: `ed303a16b`.
Native ordinary continuation entry: `e9c702f0d`.
Concrete recursive worker and equations: `359bddbb4`.
The formalization goal stays ACTIVE. This checkpoint does not complete it.
The initial pull was already up to date. Imported main remains
`153e1a211b56dd78bd22f6b427fb78e673041d55`.

## Exact concrete callback observations

EnumerationPartialExact proves exact raw singleton results for successful
representative reads, getValue and partial rendering. The proof follows each
actual read and ordered child traversal. It uses no Safe or Total premise.
SourcePruningCallbackExact extends this result through every actual pending
part, resume, oracle and recordTypes action. The private resume and oracle
helpers are reduced to their actual bodies. Existing List instances are reused.

SourcePruningAfterCallbackExact.run_exact uses the SAME recordTypes Success
receipt. A true pruning flag gives raw[]. A false flag with a stuck restart
also gives raw[]. Otherwise the result is the exact singleton with returned
metadata, the actual restart decision and the actual callback core. This is
stronger than the earlier exclusion of successful rows. It does not replace
an unsuccessful bounded callback's fuel error with an empty stream. The old
AfterCallback theorem declarations stay unchanged.

## Separate one selected prefix from its ordinary continuation

SelectedStep.runPrefix performs the original read and recursion check once.
It retains the original parked adapter and its raw restart. The false branch
runs actual preparation, native advancement, pending replacement, index
adaptation and the concrete Right callback. It leaves ordinary = none.
prefix_no_ordinary proves this property for every input and bound.

finish adds the legacy ordinary scan to the accepted Right observation.
run is finish(runPrefix). Its declaration type and instance order stay exact.
run_eq_legacy equates the ENTIRE result to the literal original worker body,
for all inputs and bounds, including malformed, missing and error observations.
The frozen body equals the base body after indentation and line-break removal.
Result, the entire Valid proposition and all six earlier theorem declarations
are unchanged. The source-boundaries.json file retains these comparisons. The existing
complete theorem passes again with its same original-selection assumptions.

NativeOrdinaryContinuations.run enters once. The same ordinary node and
nonterminal-bucket gate supplies the hook-aware alternative scan. The wrapper
retains its actual raw entry observation for all cases. identity_run gives
exact equality with the embedded legacy ordinary result for every input and
bound, including stops. Terminal and nonordinary outer entry remain unsupported.

NativeContinuations generalizes ONLY its Output and Reason universe parameters.
This permits concrete native states and selected diagnostic receipts. The
existing runtime bodies and theorem proofs do not change. Identity equivalence
still passes. The former Type-only carrier cannot hold these richer payloads.

## Actual bounded recursion

SourcePruningEnumerationRecursive.run computes the source stop test and next
selection once. resume consumes that observed Option Next. None emits the
current metadata. Done emits the source Nothing result. Stuck rejects the
branch. These decisions need no recursive fuel. Only Expand spends depth.

The selected prefix runs with one workFuel for its bounded operations. This
uniform bound is a runtime interface. No current theorem derives its sufficient
value for an arbitrary recursive history. The old selected-step completion
chooses several bounds separately. Do not treat it as this missing theorem.

A parked singleton feeds its returned metadata, core and next decision directly
to resume at the framed candidate. No second read, recursion check or restart
decision is performed. A supported raw action rejection retains the actual
reached native Caller and Queries. Unsupported prefix observations stop.

An accepted Right singleton enters NativeOrdinaryContinuations with an actual
concrete continuation. continueWith runs recordTypes Left exactly once at the
completed receipt's cache. A true singleton result rejects only that branch.
A false singleton frames its returned core and restarts at returned metadata.
Errors, mixed rows and unsupported callback shapes remain explicit stops.

Recursive continuation executes before the next sibling. The returned native
Caller and Queries supply that sibling's starting endpoint. Every sibling uses
the same captured Right-returned metadata, enumeration cache and remaining
depth. Source Enumeration.hs:975-980 has this branch structure. Metadata is not
folded from one sibling's callback into the next sibling's callback.

Each Output retains Option metadata, its own cache, Caller and Queries at
emission. The aggregate final native endpoint is separate. No output cache is
assumed valid at that later endpoint. Failures retain their actual selected,
callback, entry or stopped-fold observation. Missing captured finalization can
lose an actual child endpoint, so edge none retains endpoint none. The worker
does not substitute the edge's input endpoint. Ordinary failure retains its
current entry or fold observation; it does not retain every earlier prefix.

## Checked execution statements

continueWith_exact derives the actual concrete continuation from the successful
callback receipt. resume_stop, resume_done, resume_stuck and resume_exhausted
state the exact base decisions. resume_parked states the exact reuse of the
parked restart. completed_head combines an actual captured complete receipt,
the actual successful false Left callback and its actual recursive result.
The sibling starts at that recursive result's Caller and Queries. Both complete
and stopped suffixes remain in the result equation. This is a conditional
execution theorem. It is not initial-input completion or language preservation.

The first generic theorem application exposed distinct generated matchers in
otherwise identical printed types. Full-argument diagnostics identified this
point. Splitting the ACTUAL suffix result reduces both matchers. It retains
both cases and introduces no supported-suffix or completion assumption.

## Verification and retained attempts

Lean 4.34.1 checks all ten changed modules with warningAsError and linter.all.
There are 27 strict attempts: 11 pass and 16 fail. Every failed source and raw
log is retained. The failures include private-helper goal reduction, a reserved
prefix identifier, Unit patterns and constructor-name lint, unreduced action
matchers, the rich payload universe and the distinct generated suffix matchers.
No linter is disabled and no placeholder or native-evaluation axiom is added.

Eight serial helper builds pass. Installed Audit passes in 3780 jobs and checks
77042 theorem dependencies. The strict Audit source checks the same count.
The existing unused inputs warning in InternedFreshOrdinaryClosedCompletion
is replayed by Lake. That source stays unchanged. New strict modules have no
warning. No Haskell suite or formatter is needed because Haskell is unchanged.

Installed public readback passes for 28 declarations and eight full definitions.
It retains 1617 lines and 116720 bytes, SHA-256
`ff74f12de2fb86a6a07a7d6e5b93c6894e78c832c76950325f318186a72c0b36`.
No ellipsis is present. All reported axioms belong to propext, Classical.choice
and Quot.sound. Heavy jobs run serially with a 4G memory cap and a five-minute
limit. Commands, source snapshots, logs, reports, peaks and boundary comparisons
are in `lean/restart-evidence/20261026-native-recursive-hooks`.

## Current strongest claim and remaining work

H6 remains SourceCurrentColdFiniteWarmCalls.constructed_node_calls. Covered
closed construction and valid initial constraint allocation history derive a
complete prescribed finite node-call trace, sufficient finite fuel and one
mathematical word width chosen after construction. With empty inherited
payload, the final available value has exactly the initial finite-tree
language under the modeled formula and entailment interfaces.

The recursive worker is now concrete. Its current equations do not strengthen
H6 to whole typing/pruning enumeration. The next work is to derive a common
workFuel and a prefix invariant packet from the original selected inputs.
Then preserve the native Post, cache validity, pending references and dependency
history through actual recursive results and into the next sibling. Retain
per-output endpoints and prove any required heap transport explicitly.

Derive fuel and native numeric capacity from the INITIAL input for prescribed
finite recursive histories. More fuel is not a capacity proof. Do not add a
future successful callback, future valid cache or future numeric-range receipt
as an initial admission assumption. Terminal/nonordinary outer fallback,
native Graph correspondence, whole-driver output language, concrete solvers,
physical containers, machine Ints, extraction and arbitrary lazy demand remain
separate obligations. No convergence or practical resource bound is claimed.

No Haskell source changes in this checkpoint. FINDINGS retains all six merged
repairs and the existing external Sized documentation repair action.
