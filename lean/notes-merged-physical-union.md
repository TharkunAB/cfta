# Physical union language bridge

`MergedPhysicalUnionTransport.lean` proves that a prepared available record
keeps its exact finite language through later cache growth.
`MergedPhysicalUnion.lean` proves the language of the actual `makeUnion`
computation. This is the constructor model for the source `createUnion`.

The main result is `MergedPhysicalUnion.makeUnion_actual`. Its premises are
the initial `Context`, the actual operand records, and their initial
`Available` proofs. The result supplies all three facts at the actual
returned cache:

- The prepared context remains valid.
- The returned complete record is available.
- The returned record accepts a term exactly when an original operand
  accepts that term in the initial cache.

The proof follows every constructor branch. It removes literal empty
operands, flattens stored unions, and removes duplicate source identities.
Coherent resident records make equal source identities equal complete
records. The ordinary branch reads and combines the original complete
edges. Canonical edge ordering preserves membership. An edge with a
literal empty child cannot have an accepting run. Complete node and union
readback lemmas cover both cache misses and existing cache hits.

`makeUnion_common` separates construction from observation. It proves the
same union equation when every operand and the result use one common
observation cache. It needs `Facts` and available constructor inputs in the
construction cache. It needs no prepared context for that common-cache
equation.

`MergedPhysicalUnionTransport.accepts_stable` then relates the initial and
actual returned caches. A prepared Mu read replays its exact stored-body
unfolding result. Its successors are already available in the initial
cache. Induction over finite accepting runs transports acceptance in both
directions. This old-root theorem needs cache `Grows`; it does not need a
`NoNewMu` premise or an independently assumed final context. The actual
union constructor derives its final context through the existing ordinary
constructor proof.

The graph is `MergedPhysicalLanguage.graph`. It uses exact stored
constructor rows, the supplied interpretation of the complete guard, and
actual stored-body unfolding for Mu successors. The result does not extend
the established preparation fragment. It does not prove that the full
recursive merge schedule terminates, that an arbitrary guard interpreter
matches Haskell, or that the complete equality fixed point terminates.
The retained recursive union repair can use this result without replacing
its retained union by an eagerly exposed ordinary node.

Validation on 2026-10-13: Lean 4.34.1 compiled both modules and their
dependencies, 231 jobs. These modules make no production source change.
