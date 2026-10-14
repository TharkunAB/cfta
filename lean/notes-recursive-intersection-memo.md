# Completed recursive caller replay and memo provenance

Original node-layer checkpoint: `bf98ccfe`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Operations.hs:intersectOpen`, `intersectOpenEdge`, and the
canonical domain and constructor caches.

## Actual completed replay

`SourceRecursiveIntersectionReplayEffects` proves replay of completed
constructor work, physical payload lookup, and canonical domain allocation.
Domain allocation retains its original shifted identity. Both source cache
families remain unchanged at the later state. Ordered successful walks
replay the same values at each original position.

`SourceRecursiveIntersectionReplayCalls` composes original binder lookup,
guarded child calls, matched row occurrences, and ordered union requests.
`SourceRecursiveIntersectionReplayMu` composes canonical domain reuse, the
actual original body request, and completed optional-binder construction.
The proof retains the complete returned values and cache effects. It does
not assume callback purity, key stability, or output equivalence.

`SourceRecursiveIntersectionKernel.execute_replay` derives replay for the
full bounded uncached recursive kernel. Its premises are the original valid
machine, original domain and operand availability, actual completed execution,
and later constructor/domain growth. The returned value is identical. The
entire later machine is unchanged. `execute_larger_replay` derives the same
result at every larger bound. No preparation or depth-zero restriction is
added. The original call must have completed. This does not prove a sufficient
bound or successful first-run completion for every input.

## Checked native keys

`SourceRecursiveIntersectionMemo.requestKey` uses the actual source flat key.
It retains the shifted domain identity and ordered tagged operands. An
unresolved operand retains the source memo bypass.

`KeySafe` requires a positive word width, a domain identity in the nonnegative
signed range, and checked complete operand codes. These remain explicit
source machine-range premises. `requestKey_nonnegative` derives the native
publication first-key contract. No supply-overflow theorem is assumed.

`requestKey_injective` derives equality of the complete physical request from
equal checked machine triples. The proof uses the actual domain-cache
representation and canonical physical record lookup. It includes the reserved
empty domain. `swapped_key_eq_iff` proves that reversed unequal operands have
different native memo keys. The independently sorted cutoff pair does not
normalize the outer memo key.

## Concrete completed entries

`Produced` records an actual complete recursive kernel execution, its original
valid inputs, finite bound, returned cache, and later growth. `produced_here`
constructs this evidence directly from execution. `produced_grows` retains it
after later source effects. `produced_spec` derives current original-domain,
operand, and result availability. Results of open calls can be RecIntersect
placeholders. Availability does not assert closedness.

`MemoValid` requires concrete completed provenance for every stored key.
`memo_empty`, `memo_grows`, and `memo_insert` derive initialization, retained
provenance, and first-writer insertion. No arbitrary compute or language law
is supplied.

`memo_hit` combines actual native-key injectivity with concrete execution
replay. It derives result availability and a finite bound at which the current
uncached kernel returns the stored value without changing either current
cache. Every larger bound returns that same observation.

This is the completed-value layer. It does not publish only completed values
as a replacement native algorithm. The source can publish a key whose value
is still an unevaluated thunk. Pending publication and forcing need their own
operational correspondence.

## Next obligations

Completed edge provenance and typed pending thunk observations are now proved
in `SourceRecursiveIntersectionEdgeMemo`, `FlatMemoThunk`, and
`SourceRecursiveIntersectionThunks*`. Checked keys identify the original
physical request in every thunk phase. Publication precedes forcing. Demand,
completion, source growth, and completed native observations preserve concrete
provenance. Read [native memo thunks](notes-recursive-intersection-thunks.md).

The complete branch compiler and recursive native driver now thread both
memo families. Exact request steps, continuation composition, finite traces,
and physical-effect retention are checked. Derive whole completed-run
correspondence and memo provenance from those actual native traces. Do not
supply provenance at completion frames or assume purity or product language.
Read [native recursive execution](notes-recursive-intersection-native.md).

Then derive the physical input view, finite reachable payload inventory,
sufficient execution bounds, and product-row membership and rejection.
`product_exact` can then give product language. New Mu bodies still need
preparation or a larger cold-exposure invariant. General open nested first-run
completion, native thunk forcing, runtime primitives, and verified Haskell
extraction remain open. The existing Sized and cold-table proofs remain.

## Original node-layer validation

All five modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,223 jobs and 40,615 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-recursive-memo-20261014-audit.log`.
No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. Prior proof, draft, and fixture bytes remain preserved
against the saved manifest.
