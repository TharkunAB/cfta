# Stateful recursive intersection caller

Proof checkpoint: `95792559`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Operations.hs:intersectOpen`, `onNode`, and
`intersectOpenEdge`.

## Executable caller

`SourceRecursiveIntersectionKernel.Machine` retains the actual constructor
and domain caches. `onNode` reads the checked physical source branch selector.
Its recursive callback receives the actual returned caches. The port includes
empty, reset, self, swap, repeated pair, one or two Mu operands, unions, references,
and ordinary nodes. It supports guarded edges. The empty guard and guard
conjunction are explicit source operations.

`mu` allocates the extended canonical domain before the actual body request.
It then runs the checked source `maybeMu` in that request's returned heap.
`reference` recovers the complete original bound Mu. An absent domain binding
and an absent physical payload remain separate. Valid source domains exclude
the latter local lookup failure.

`edge` checks arity before child calls. A mismatch builds the source empty
edge. Equal arity evaluates zipped children in order, conjoins the original
guards, then interns the edge. `node` retains equal-symbol hash-join occurrence
and bucket order, evaluates those edge requests, then interns the canonical
surviving node. Union branches evaluate ordered member requests before union
construction.

`execute` supplies bounded uncached recursion to `onNode`. Exhaustion reports
its own failure and retains the actual current caches. It never substitutes
an empty result for exhaustion. Constructor pending, absent bindings, absent
physical payloads, and unsupported operands also remain distinct.

The outer native node and edge memo tables are not included in `execute`.
This is the source caller kernel, not the complete native `intersectOpen`.
Native memo hits can bypass work. Their actual cache effects and pending lazy
publication still need a wrapper proof.

## Derived invariants

`SourceRecursiveIntersectionKernelFacts` defines the caller's complete cache
invariant and growth history. A valid domain retains its actual allocated
identity, canonical key order, typed original Mu bindings, and their complete
physical records. These facts survive later constructor and domain effects.
Ordered walks retain each returned available value at the final cache.

`SourceRecursiveIntersectionKernelCalls` derives actual Mu-domain allocation,
body availability, original-bound-record lookup, guarded child requests,
resident edge results, and node results. `execute_checked`
proves these invariants for the full recursive kernel at every bound.
Both successful and failed outcomes retain source facts, physical growth,
issued-node history, and domain-table growth. Every successful result is an
available source value. Open calls can return RecIntersect placeholders.
No recursive callback invariant is
assumed in this final theorem.

## Stable bounds and literal row readback

`execute_stable` proves that every reached result other than
exhaustion remains identical at every larger bound. The equality includes
pending keys, other failures, and complete returned caches. This is a
stability theorem. It does not derive a sufficient bound for every input.

`walk_done_iff` derives the actual ordered request trace from
executable completion and proves the converse. Each trace retains the complete
returned value and intermediate cache. `WalkTrace.length` preserves positions.

`edge_readback` derives the actual child trace, subsequent edge construction,
literal symbol, conjoined original guard, and ordered actual child values.
It includes canonical cache hits. `edge_mismatch_readback` derives the source
empty edge without child calls. `node_readback` derives the actual matched-row
trace and precisely the parent's canonical surviving physical edges. These
theorems use `execute_checked` to discharge their callback invariant for
actual bounded recursive calls. No product-language or equivalent product-row
contract is supplied.

## Next obligations

Completed full guarded kernel replay and native-key node-entry provenance
are now checked at `bf98ccfe`. Hits derive exact finite replay without changing
either later cache. Read [recursive memo](notes-recursive-intersection-memo.md).
Next connect edge provenance and the native recursive node/edge memo wrapper.
Keep shifted domain identity, ordered tagged operands, reversed swap requests,
RecIntersect bypass, and pending publication before value forcing.

Derive the physical input view and finite reachable payload inventory. Connect
the actual recursive requests to the existing semantic schedule. Derive a
sufficient bound. General open nested binder
completion still needs key separation or a larger execution invariant.

Use the literal row readback to derive
`SourceCyclicRowsNativeGate.ProductReadback.members` and `.rejected`.
`product_exact` then derives product language. Compose the cold shared-table
and Sized adapters. Do not substitute an
assumed product-language equivalence. New Mu bodies need derived preparation
or a larger cold-exposure invariant. The guard parameters still need their
existing source logical interpretation. Native runtime and dependency
correspondence remain separate from these handwritten source models.

## Validation

All six modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,218 jobs and 40,573 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-recursive-kernel-20261014-audit.log`.
No Haskell source changed. The prior passing Nix and formatter checks remain
the source validation checkpoint. All prior proof, draft, and fixture bytes
remain preserved against the saved manifest.
