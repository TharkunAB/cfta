# Native selected-step runtime and continuation infrastructure

Narrow adapter: `01a2f779f`. Continuation fold: `80968dad4`.
Selected worker and completion: `38a2df471`.
Per-receipt native posts and pending history: `549061e9f`.
The formalization goal stays ACTIVE. Origin/main remains
`153e1a211b56dd78bd22f6b427fb78e673041d55` after the initial pull.

`SourcePruningEnumerationSelectedStep.run` executes one selected read and
recursion check. It retains unsupported read shapes and errors in `stopped`.
It does not select the variable again at a later cache.

The repeated branch retains the actual checked core. The parked adapter
rebuilds the selected flag and removes the full old suspended bucket from
waiting counts. It then attaches the checked core. Restart runs only when
this adapter returns a cache. The restart raw result distinguishes stuck
rejection from a stop-rule result, exhausted work and another selected variable.
This stage does not execute that next variable.

The false-check branch runs the actual narrowing preparation. It retains
the reached native Caller and unchanged query memos, including the native
heap returned by failure or Empty. Empty supplies the rejection action. Its
raw result is empty; the runtime does not invent a post-rejection cache or
invoke the Right callback.

For a supported nonempty result, the runtime executes the returned action.
Equal handles require no pending-slot write. Changed handles use the actual
representative read and pending-slot write. The runtime retains action errors
and unsupported observations. It does not convert them to successful rows.

`NarrowAdapter.adapt` frames the observed core for equal handles. For changed
handles, it runs `NativeIndex.write` with the full suspended bucket as both
lost and gained references. This rebuilds the candidate flag and waiting
counts. It then attaches the exact observed core. This is an index adapter;
it does not repeat the native narrowing query or the original action.

`adapt_after_write` uses the actual pending write and indexed-write receipt.
`complete` derives sufficient adapter fuel, with every additional fuel value,
from the equal or changed receipt. It requires no future adapter-success
premise. Arbitrary bounds can still return `none`. These receipts do not
make every optional candidate a verified cache.

The Right callback runs at the attached core. The concrete recordTypes_inr
theorem gives its exact pure result: false and the same metadata, at the
same core, for every callback fuel. The runtime retains this singleton row.
It frames the actual callback core with the attached indexes and then runs
NativeOrdinary. The current ordinary scanner does not yet consume a recursive
continuation hook. Terminal and nonordinary outer parents retain the actual
entry raw result with no shallow ordinary scan.

`SourcePruningEnumerationNativeContinuations.run` supplies that separate fold
infrastructure. It calls the supplied hook only on an actual completed edge
receipt. The hook runs before the sibling. Its returned Caller and Queries
feed the sibling. The captured enumeration cache and suspended bucket stay
fixed. A closure can supply the same metadata to each sibling callback.
Descendant recursion can use the callback's updated metadata inside the hook.

Valid edge rejections skip the hook and retain reached native effects.
A completed hook with empty output continues siblings. A stopped hook retains
its output, reason, completed edge receipt and optional reached endpoint.
Missing and unsupported edge results remain explicit. No endpoint is invented.
Order and duplicate edge receipts remain intact.

`completed_head` and `stopped_hook` expose the execution equations.
`identity_run` equates the identity-hook worker with the entire embedded legacy
`NativeBranches.run` result, including stopped receipts. The fold does not
establish full callback or recursive-driver effect correspondence. It does not
claim lazy demand behavior for an externally abandoned result stream.

## The original selection derives the complete selected worker

prepared_action identifies the actual nonempty preparation action. Equal
handles use pure unit. Changed handles use the actual representative read
and pending write. prepared_singleton inverts an actual success and derives
the exact singleton raw result at that same fuel and final core. It uses
representative_exact and the actual write shape. It assumes no Safe cache
or general future determinism law. This closes the raw observation needed
by the executable worker's singleton match.

run_parked, run_empty and run_narrowed state exact equations for the whole
selected worker from its actual earlier observations. They do not call a
second read/check producer. run_narrowed executes the concrete Right callback
and retains the exact NativeOrdinary observation at the reached Caller/cache.

complete starts from Context, Safe, global pending history, original pure
selection, realized native handles, representative roots, canonical counts
and candidate flags. It calls SelectedOrdinary.complete_with_history once.
The same witnesses supply both repeated and false-check branches.
No successful future action, cache adapter or continuation is an input.

The theorem derives read, check, native, representative and index bounds.
Every larger read, check and index bound gives Valid for the full worker.
Callback fuel and the five ordinary bounds stay arbitrary in this first
observation. Thus Valid does not assert that arbitrary ordinary bounds finish.
The native narrowing and representative bounds are the chosen witness bounds;
the theorem does not quantify larger values for those two bounds.

Valid exposes exact read/check receipts. The parked branch has Safe,
CacheValid at the unchanged Caller, pending history, the same counter,
preserved dependency levels and its actual restart observation. The narrowed
branch retains actual prepare equality, reached native Caller, original-to-
reached Post and unchanged query memos. Empty retains raw[] and no later stage.
Nonempty results retain Safe, CacheValid, Pending, Ready, the stored pending
handle, unchanged waiting counts and the exact Right and ordinary observations.

The ordinary capability requires an actual node, a nonterminal suspended
bucket, selected-edge membership and Ranges at the reached Caller/cache.
It derives finite ordinary bounds for the SAME FULL selected-step worker.
Only ordinary bounds change in that equation. All prefix fuels, checked core,
prepare result, reached native state, action, cache and Right rows stay fixed.
Every larger ordinary bound produces that same entered cache and scan result.

The packet retains the final Post and saved queries. Each processed receipt
retains Admitted, pending references, its actual native advance endpoint,
Post from the original Caller, saved query state, fragment history and
concrete Left callback capability. An unsupported annotation retains the
first unhandled receipt. Supported annotations give the complete scan result.
These callback capabilities remain per-receipt availability. They do not
execute callbacks between the current scanner's native alternatives.

## Verification and evidence

All five changed modules pass Lean 4.34.1 strict checking with every linter
and warnings as errors. Thirteen strict attempts retain six failures and
all actual source copies. The adapter repairs reduce both Option count binds
and use current conditional lemmas. The continuation repairs remove unused
simp arguments and explicitly reduce the known endpoint match. The completion
repairs use current conditional lemmas and place required DecidableEq
instances after the generic action helpers. No linter is disabled.

Five installed helper/consumer builds pass. Aggregate Audit passes with
3774 jobs and 76960 theorem dependencies. The checker body remains exact;
Audit adds two imports. The existing unused inputs warning is unchanged.
The dependency count is an audit count, not a completion estimate.
The final receipt-output strengthening requires a focused completion check,
installation, public readback and Audit rebuild. Earlier passing artifacts
remain in the evidence. All 22 checks run serially under 4 GiB caps.

Installed public readback checks 25 declarations and axiom sets. It prints
full Valid, selected runtime and continuation runtime definitions. The final
output has 1551 lines and 128546 bytes, with no ellipsis.
SHA-256: `c750dbe857270175406dbbf5962cd62b5cc4ad120c648a3a39d0f83172a4f6f5`.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The earlier public output remains separate. No project or native-evaluation
axiom is added. Independent source reviews check original inputs, actual
endpoints, same producer witnesses, index recovery, all full-worker equations,
per-receipt histories and the supplied-hook boundary.

Evidence: lean/restart-evidence/20261026-native-selected-step.
The manifest records exact payload bytes and SHA-256 for raw logs, every
strict input, public readbacks, source snapshots, original Audit, proof diff,
verification report and cap records. The report also hashes all relevant
unchanged source files against the base commit. Force-add exactly the manifest
payloads. Verify indexed and committed bytes before the authorized push.

## Next composition

Wire the actual Left callback and a fuelled recursive selected step into
NativeContinuations. Use each receipt's own Caller/query/Post and branch cache.
Use initial dependency levels and pending-ID bounds to derive callback
completion. A pruning or stuck result completes that branch with no output;
it still retains all reached native effects before the next sibling.
Keep errors, unsupported outcomes and optional missing endpoints explicit.

The present SelectedStep still calls the old NativeOrdinary scan. Do not
postprocess an eagerly completed sibling list and call it source interleaving.
The new hook-aware fold must execute recursive continuation before evaluating
the next sibling. Each sibling restores the original captured enumeration
input and receives the same incoming metadata. Each callback's returned
metadata belongs to that branch's recursive continuation.

Derive initial-only native query capacity across narrowing, alternatives and
recursive calls. Extra fuel alone does not establish machine-word capacity.
Retain native Graph correspondence, terminal/nonordinary outer fallback,
pruning language laws, concrete solver behavior, extraction, finite-machine
correspondence and exact Haskell demand boundaries as open obligations.

Haskell source and H6 remain unchanged. H6 retains its construction, cache
and history premises. This checkpoint does not prove the full native driver,
initial-only resource admission, extraction correspondence or convergence.
