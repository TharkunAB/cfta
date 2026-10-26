# Native selected-step runtime and continuation infrastructure

Draft. Verification and the final selected producer remain TODO.

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

The Right callback runs at the attached core. The runtime retains its raw
result, including pruning and errors. Only a successful singleton with a
false pruning flag enters `NativeOrdinary.run`. It frames the actual callback
core with the attached indexes. The callback raw result retains its updated
metadata. The current ordinary scanner does not yet consume a recursive
continuation hook.

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

TODO — Final selected producer: record the checked same-witness theorem and
its exact initial hypotheses. State ordinary admission at the actual narrowed
Caller, callback cache and entry endpoint. Do not claim that initial Context
alone supplies ordinary numeric ranges. Retain parked, Empty, callback-pruned
and unsupported cases explicitly. Connecting this producer to the supplied
hook and a fuelled recursive driver remains separate work.

TODO — Verification: insert actual strict attempts, repairs, installed checks,
complete public signatures and axiom sets, Audit results and artifact paths.
The NativeContinuations checkpoint is commit `80968dad4`; its source SHA256 is
`cb816986cd5c059a314f7e578ec5e43a9802606db2cc9f1788026d9c06b7923c`.
Do not infer publication outcomes from these identifiers.

Haskell source and H6 remain unchanged. H6 retains its construction, cache
and history premises. This checkpoint does not prove the full native driver,
initial-only resource admission, extraction correspondence or convergence.
