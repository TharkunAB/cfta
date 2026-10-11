# Complete pruning schedule and concrete candidate semantics

The source is `Data.CFTA.Refinement.Prune`. `PruneSchedule.lean` now includes
its `InternedUnion` branch. It prunes each union member, rebuilds the union,
and caches the result by the original identity. The model already includes
ordinary nodes, bare recursive references, recursive binders, ordered child
traversal, equality narrowing, empty-child removal, and the semantic pass.

`PruneCandidates.lean` proves the source candidate loop. A successful loop
has exactly two forms: it completes every query and returns precisely the
Yes candidates, or an ambiguous Unknown restores the whole original edge.
The restoration discards the partial accumulator. An unambiguous Unknown
returns an error. `semantic_exact` also covers the Top and recursive-guard
retention branches.

`prune_semantic_exact` instantiates this loop with the executable cyclic graph
specialization in `ObservationGraph`. The candidate union and each stored
observation are proved correct by that module. The theorem preserves the
language of the declared semantic root guard when sparse query decisions
are sound. It requires no solver-completeness premise. Residual guards and
equality conditions can remain in the original graph's edge predicates.
Unknown fallback keeps the complete declared guard. The weaker confirmed-Yes
interpretation has a separate `prune_exact` theorem.

`PruneCorrectness.schedule_exact` proves all three mutually recursive driver
invariants for every successful bounded execution:

- Each returned node has exactly its input node's complete language.
- Child lists preserve length, order, and every child language.
- Edge lists preserve their full union language.
- Every cached identity pair has equal languages.

The proof follows every source branch. It proves cache validity at insertion
and uses that invariant on hits. It proves the result of each binder body
before rebuilding, then composes every subsequent re-pruning step. It does
not assume that the recursive driver preserves its input language.

`Laws` lists the remaining local operation requirements. They are: node-row
meaning, node construction, union-view meaning, union construction, child
replacement, equality narrowing, empty-child soundness, binder rebuilding,
and successful semantic evaluation. The evaluator must preserve the pruned
identity cache. This matches the source, where specialization modifies only
`splitMemo`, which is absent from this driver projection.

Several of these requirements have concrete proofs:

- `edge_replace_exact` proves the transition constructor's child replacement.
- `edge_empty_child` proves elimination from actual child acceptance.
- `binder_rebuild_exact` derives recursive congruence and source cleanup from
  `BinderLanguage.least_congr` and `cleanup_exact`.
- `prune_semantic_exact` derives complete candidate evaluation for the
  `ObservationGraph` guard fragment, including Unknown fallback.

Open-body equivalence must hold under every environment. `shapeMeaning`
includes the environment in its semantic input. `binder_needs_uniform_body`
proves a counterexample to checking just one environment: a free reference
and a constant leaf can agree there, but their least recursive binders differ.
The source's fresh-name substitution adapter must connect `createMu` and
`substFree` to this uniform body law. `BinderSubstitution` supplies the local
substitution theorem with its explicit freshness condition.

These results do not establish all Haskell adapter laws. Exact source
`reduceEdgeIntersection`, identity allocation, fresh-name reconstruction,
and the split-memo relation still need to connect to the local theorems.
`ObservationGraph` verifies its declared guard fragment. The full source
substitution-sensitive signature and sparse guard evaluator need their own
observation correspondence. Binder-aware specialization must also establish
that its cache key remains sufficient as the binder table grows. No theorem
here treats tests, generic primitive contracts, or finite graph examples as
proofs of those source adapters.

Fuel exhaustion is a model execution error. It is never an empty language.
The success theorem does not prove termination of repeated recursive pruning
or external solver calls. Public input validation and source IO behavior
remain separate from this pure schedule.

Validation: `lake build MicroCFTA.PruneCandidates MicroCFTA.PruneCorrectness`
succeeds with the pinned toolchain. There are no proof placeholders.
