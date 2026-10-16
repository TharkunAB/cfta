# Independent direct probes of admitted checked queries

Date: 2026-10-16 07:24 CEST.

Reviewed frozen source: `SourceCurrentAllocatedNativeAdmittedQuery.lean`,
125 lines, SHA256
`c908056843957d5e6c84fdca258aba59365aa8d4408c41b7ec01a31915731e5b`.
The source hash was checked before and after the probes. No source was edited.
No canonical Lake build was run. Root reported GREEN1130 for the final build.

## Direct checks

Pinned Lean 4.34.1 command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-semantic-admission/admitted-query-independent-probes.lean
```

The command returned terminal 0 with no warnings.
Two public axiom reports and two full public signatures passed.
Both public theorems use only propext, Classical.choice, and Quot.sound.
Three kernel integrations passed:

1. query_complete derives an actual checked execute `.done` at fuel+1,
   an empty free list, and exact physical intersection language under every
   output environment. These conclusions concern the same value and complete
   checked final state. No target-model law or target-domain validity premise
   is supplied by the probe.
2. The same receipt derives actual result availability, Original syntax,
   loaded fields at the final operations and heap, scoped returned cells,
   and final Idle. Original follows from final coherence and closedness.
3. Actual source/target heap growth and root inclusion derive Agreement.
   An old valid input remains admitted with an iff at its identical rank.

## Exact assumptions

The query endpoint takes an old source heap and its Facts, a finite list of
closed Original available old roots, formulas and solver interpretation,
and the actual current checked state. The current state supplies physical
Good, semantic heap readiness, scoped returned cells, and Idle. Source heap
records and issued history extend to the current heap. Both next operands
are available and closed there. Reached WordRanges remain explicit.

The old semantic cache premises are explicit and nontrivial:

- Contextual under the old fixed finite input model supplies the actual
  returned node and edge soundness/completeness laws.
- Admitted independently covers both old node operands and every old edge
  operand child. It prevents transport of a law that was only conditionally
  true for an unadmitted request.
- SeenAdmitted covers both names of every seen pair in each returned request
  domain. It supports both sound and rank-bounded complete context transport.

The endpoint constructs the larger current-heap root inventory itself.
It derives the next operands' Original syntax and model validity from their
closed availability. It derives old/new rank Agreement from physical growth,
then transports the same warm returned-cell laws. It invokes the existing
checked WarmQuery theorem with that derived larger model. There is no supplied
parent result, future completion callback, desired target-model law, or
future result heap invariant.

## Remaining causal coverage boundary

The endpoint does not derive Admitted or SeenAdmitted for newly returned
internal requests after this query. They remain assumptions for the old cache
at this invocation. Initial empty caches satisfy them, and constructor-only
advances retain them, but arbitrary repeated inventory expansions still need
an actual checked-trace proof that publishes new admitted request operands
and seen-pair names. The new Receipt does not by itself close that induction.
This is a one-step semantic admission theorem with explicit old coverage.
It must not be described as a fully derived dynamic Scan semantic invariant.

No material proof or scope defect was found in this bounded inspection.
Runtime initialization, pending publication, native identity correspondence,
solver behavior, and GHC forcing remain the existing external adapters.
