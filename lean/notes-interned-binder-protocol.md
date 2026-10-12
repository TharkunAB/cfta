# Stable identities through the two-probe binder protocol

`InternedBinderProtocol` proves structural identity reuse. It does not use
language equivalence to identify nodes.

`Work` records a finite effect computation. Each interning request performs
the source lookup first. A miss reserves an identity, installs the canonical
entry, and then runs the delayed body-identification computation. A hit skips
that computation. Continuations can use the identities returned by earlier
requests. Both probe computations and body computations can intern more nodes.

`run_steps` derives a finite `Cache.Steps` trace from this executable worker.
It includes the counter reservation and installation for every miss.
`run_valid` derives cache validity, and `run_grows` derives persistence of all
previous entries. `stored_key_finite` constructs a finite covering list from
the issued entries below the actual counter. It does not use an injective
encoding of all possible structures or an infinitely populated cache.

## Exact source key and readback

`createMu` models the raw `createMuDontCleanup` protocol. It runs the body at
`RecDepth`, reads that result's depth, runs the body at `RecUnint` of that
depth, and includes both resulting node identities in `MuKey`. The callback
function is absent from key equality, as in `UninternedMu`.
The body at `RecInt` of the selected identity runs after installation on a
miss. Binder cleanup remains the separate proved constructor step.

`NodeKey` retains all source key alternatives: ordinary edge-identity lists,
empty, union-member lists, and the pair of Mu probes. `NodeRef` retains the
source constructor tags and identities. The memo reference type includes
interned, uninterned, depth, intersection, and FTA-state references.

`createMu_readback` derives that the final table stores the returned entry
under the key computed by those actual probes. `replay` proves that every
completed effect computation returns the same result after any extension of
its final table. The replay leaves the entire state unchanged. Thus it does
not reserve another identity or repeat a missing body computation.
`createMu_after_steps` specializes this result to arbitrary later finite
atomic cache operations. It derives both the same complete entry and the
same two-probe key.

`warmup` executes a finite request family. `finite_replay` and
`finite_identity_image` derive one fixed finite result and identity image for
every later request from that same family. The family is an explicit list of
computations. No repeated-result law is supplied as a premise.

## Binder substitution memo

`bindings` executes free-key restriction, ascending order, duplicate removal,
and omission of absent map entries. `MemoKey` includes the original source
node and the complete retained binding list. `memoKey_congr` proves that
changes outside the free-key set do not change this actual serialized key.

`memoReadback` applies the source first-writer rule and reads the stored whole
node. `binder_memo_replay` proves exact node and identity persistence even
when a later call proposes a different candidate or changes irrelevant
environment bindings. This is a completed memo readback theorem. It does not
model the evaluation of a recursively forced unfinished memo thunk.

## Callback contract and supported constructor fragment

The source requires a parametric Mu body. The comment above `InternedMu` in
`Interned.Type` explicitly states that arbitrary functions can inspect their
argument and that the requirement is not checked. The `createMuDontCleanup`
documentation gives the substitution equation for its variable choices.
Totality alone does not establish that equation.

`exotic_probes_incomplete` retains the concrete counterexample: return one
node for `RecDepth` and `RecUnint`, but another node for `RecInt`. Both probe
keys equal the keys of a constant callback. Their actual-identity bodies
differ. This is a documented unsupported callback, not a new source defect.
No claim equates arbitrary callbacks merely because both probes agree.

`RootTemplate` is the exact normal fragment that returns its local argument
or one captured source node. `root_probes_complete` derives the entire
template from the two probes in that fragment. The second probe prevents a
captured probe-shaped node from being mistaken for the local argument.
`rootStored_depth` derives unchanged depth metadata across all variable
choices. `matchMu_cached` follows the actual stored-probe dispatch before
general substitution. `constructed_root_roundtrip` derives canonical identity
reuse from a completed template construction, with no separately assumed
cache-presence or metadata-coherence premise.

## Remaining representation boundary

The general replay theorem is for the same fixed effect computation. It does
not establish that dynamically rebuilt lexical instances form one fixed finite
family of computations. The missing bridge must derive that fact for ordinary
constructor contexts and nested Mu templates. Those contexts perform separate
edge and node interning and read cached depth and free-variable metadata.
This module models node-cache effects; it does not conflate the source's
separate edge and node identity supplies.

The runtime binder-result cache can reuse a body built under another source
identity. Connecting that result to the finite lexical inventory still needs
the two-cache constructor readback and the full structural callback contract.
The root-template theorem is not a proof for every HOAS callback or every
nested constructor template. Therefore `LexicalBoundedBuilder.RowsCorrespond`
and the complete finite runtime exposure identity image remain open.

The execution model is sequential within a completed request. Existing
`Cache` theorems cover atomic first-writer identity readback under races.
This module permits arbitrary later atomic steps; it does not prove every
possible lazy-body forcing schedule inside a racing request. Typed cache
selection, hash-table storage, and unsafe runtime effects remain separate.
Natural identities describe the source before signed ordering or full-word
wrap changes apply. `InternedIdentityWords` states those machine limits.

Validation on 2026-10-12: `lake build MicroCFTA.InternedBinderProtocol` passes
(3 jobs). All 29 theorem audits use only standard Lean axioms. No incomplete
proofs, new axioms, Haskell edits, or Cabal runs were added.
