# Refinement acceptance and Unknown

`MicroCFTA/AcceptanceEffects.lean` models the global `undecided` flag in
`Data.CFTA.Refinement.Denotation.accepts`. It extends the verified adaptive
worker in `AcceptanceDispatch`. The proof tracks the local cache and the
global flag separately. A list of executed guard calls is proof data.

The shared worker tries alternatives in source order. Each child visit uses
the position/state cache. A cache hit does not call the guard. A failed child
skips its parent guard. The direct worker creates a fresh local cache when
it encounters multiple matching alternatives. It restores the caller's
cache on return, but retains the global flag and the guard-call list.

`shared_project` and `unshared_project` prove that these effects preserve the
previously verified Boolean worker. `shared_tracks` and `unshared_tracks`
prove that the global flag is exactly the disjunction of Unknown results
among executed calls. `shared_retains` and `unshared_retains` prove that each
execution retains the earlier calls as a list prefix.
`unshared_unknown_monotone` derives that a recorded Unknown cannot be lost.
These proofs cover both short-circuit loops, both cache branches, and fresh
local cache scopes. They do not assume that the flag composes correctly.

A stable three-way callback is an explicit input. `Compatible` identifies
each Boolean edge guard with the callback's Yes result. Under that relation:

- `accepts_confirmed` proves that Yes is equivalent to a run whose guards all
  return Yes.
- `accepts_unknown_callback` proves that Unknown is equivalent to the absence
  of such a run and an Unknown result among the calls actually executed.
- `accepts_no_decided` proves that No is equivalent to the absence of such a
  run and a decided result for every call actually executed.

These are the documented three-way outcomes. A later successful alternative
returns Yes even if an earlier alternative recorded Unknown. Unknown does
not mean that a semantic accepting run exists. It records an unresolved
query encountered by this search.

`cached_unknown_retained` checks two alternatives that revisit the same
Unknown child. There is one guard call and the final result is Unknown.
`yes_after_unknown` checks that a later confirmed alternative returns Yes
while the earlier Unknown remains in the execution record. Both checks use
kernel evaluation.

The callback is a fixed function of state, edge, and term. This is the
stability condition required when a cached result replaces a repeated
solver call. The model does not assert that an arbitrary effectful solver
is stable, that its decided results are semantically sound, or that the
Haskell IORef and Map implementations refine these pure operations. Solver
soundness and the source graph/term adapter remain separate obligations.
