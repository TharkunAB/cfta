# Current recursive equality and root union normalization

Current source update: main `24a710a3`, merged at `6a02619c`, adds a
constrained-descendant check at ordinary path endpoints. The pure current
policy and actual-record finite checks are proved in `3eed507c`. The older
stateful/memo selection pipeline below retains its earlier policy. Caller-cycle
witnesses remain historical; the preserved cold Haskell fixture now completes.
Read [the current source comparison](notes-main-24a710a3.md). General caller
termination and the new descendant memo remain open.

Source checkpoint: `origin/microcfta`, `de910ea`. The relevant source is
`Equality/Operations.hs` and `Interned/Type.hs`. No Haskell source is changed.

`ConstrainedRecursionGate` implements the current `meetsConstrainedMu`
dispatch. A `Rec` or `InternedUnion` is blocked before metadata shortcuts.
Zero nested binders and no free references permit a node. A recursive
node with constraints is blocked. A closed unconstrained binder is clear.
An open unconstrained binder follows `unfoldOuterRec` at the same path.
An ordinary endpoint is blocked exactly when it has free references.
Children consume a path index. Missing children are clear for this gate;
the separate required-path operation handles their existence.

The instrumented worker returns `none` when its fuel is exhausted. It is
not a clear result. `fuel_stable` proves that additional fuel cannot change
a completed result. `selected_iff` proves that a selected class has only
completed clear path checks. `pass_exact` proves exact constrained-language
preservation for its conservative bounded pass under `EqualityReduction.Laws`.
The original edge constraints remain unchanged.

`total` is an unbounded source worker. Its lexicographic termination measure
is path length followed by `UnfoldingRank.rank`. The rank must decrease only
when an open unconstrained binder unfolds at the same path. The theorem
`completed_agrees` proves that a completed bounded result equals this total
worker. `total_pass_exact` proves the same constrained-language law for the
total worker. Constructing this rank for actual interned source nodes is a
remaining representation obligation. The module does not claim source
termination from path length, and it does not prove termination of a caller's
repeated equality fixed point. Kernel examples show the changed decisions
and a same-path unfolding that needs more than one step at the empty path.

`RecursiveReductionBarrier` retains the previous conservative gate for
comparison. Its path-only fuel theorem applies to that gate. Its finite leaf
guard normalization results remain applicable to the current one-pass worker.

`BinderSelfUnion` models `withoutSelfReference` in `createMuDontCleanup`.
It removes only bare own references in the root alternatives. It retains
references under constructors, under another binder, and to outer binders.
`closed_iff` proves that every candidate language is closed under the body
exactly when it is closed under the filtered body. `binder_exact` then proves
equal least languages for every open or closed body. `cleanup_exact` composes
this law with unused/self-binder cleanup. No productivity premise is needed.
The filter is idempotent. Adding or removing a root self alternative preserves
the binder language even when the remaining alternatives are recursive.

This proves the semantic law used by source commit `7901500`. It does not
prove canonical interned identity equality, the `createUnion` flattening and
edge aggregation implementation, or general repeated-reduction termination.
`EpsilonUnion` continues to prove epsilon-graph language laws. It does not by
itself prove these representation properties.

`EqualityIdentityMemo` covers the new constraint identities and memo keys in
`Equality/Constraint.hs`. It instantiates the existing valid-cache invariant
for ordered class lists. `equal_exact` proves that identity comparison equals
key equality. `compare_exact` proves that the identity fast path preserves
the structural class order. This does not identify arbitrary permutations
of class lists; the public constructor itself does not sort them.
`classesAt_exact` proves correct identity readback. `descend_semantics` and
`combine_semantics` connect identity-keyed caches to surviving child equality
pairs and conjunction. Combination requires completed bounded normalization.
The existing cache validity and pure memo validity premises remain explicit.
Trie/list coherence, source class sorting, hash storage, concurrency memory
ordering, and the machine identity wrap bound are not discharged here.

Validation uses the pinned Lean 4.34.1 toolchain. All three proof modules build
without admitted proofs or native-evaluation axioms. The root validation run
also checks the unchanged current Haskell source and the retained recursive
reduction and open-union reproductions.
