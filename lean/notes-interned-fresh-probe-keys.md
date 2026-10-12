# Fresh outer references and nested Mu keys

`InternedFreshProbeKeys` proves the reference-retaining case of pending Mu
key separation. It also proves the exact source memo-key rule for an outer
variable absent from the original nested binder's free set. It does not
claim complete nested Mu construction or termination.

## Derived key separation

`Resident` means that a nonprimitive node is the complete canonical record
stored under its own entry key. `stored_resident` derives this fact from
coherent table readback. `resident_reference_injective` proves that source
node-reference equality implies equality of the complete resident records.
This includes cached free-reference metadata. Empty and reference values use
their actual constructor equality; node, union, and Mu values use canonical
cache identities.

`IssuedReferences` states that each cached free interned reference has an
actual reservation in the supplied identity history. This is a provenance
condition, not a key-separation or replay premise. `issued_free_below` derives
the numeric bound from the existing cache validity theorem. `next_absent`
then proves that the next fresh identity is absent from each such old probe.

The module proves the relevant primitive provenance steps. Interning retains
earlier issued references. Its actual recursive argument refers to the entry
just reserved. The depth and ordinary sentinels introduce no interned name.
Ordinary and union identification use only their actual children's free
references. Mu identification removes its own local reference. In particular,
`identifyMu_removes_local` returns to the older reference provenance when the
body introduces only that local name.

`fresh_probe_key_separates` follows the actual cache miss identity and exact
two-probe key. If either inner probe retains the fresh outer `RecInt`, its
key differs from the pending outer key. Equal keys would imply equal resident
probe records, including their free-reference sets, which contradicts the
derived absence of that fresh name from the old probe.

`constructed_pending_key_separates` obtains the older coherence and complete
cache-to-record relation from the existing empty-cache construction trace.
It also derives that an absent record means a genuine identity-table miss
in that completed state. The generic theorem can be used in an intermediate
state when a genuine miss and the relevant local invariants are established.

These theorems still require the probes' reference provenance and residency.
The primitive preservation lemmas do not yet derive those conditions for a
full fresh-outer-dependent nested template compiler. That compiler is the
remaining source adapter; this module does not assume its result by naming
it a valid callback.

## The independently memoized case

The actual `substitutionPlan` key retains the original binder identity and
the environment restricted to its stored free-variable set.
`absent_outer_memo_key` executes this restriction rule when only an outer
variable changes. If that variable is absent from the original free set,
the serialized key is unchanged. `absent_outer_memo_replay` then reuses a
completed earlier request without changing the memo table.

The replay theorem requires that the earlier request completed. Deriving
that it occurs during the outer probe traversal is still a statement about
the full generated nested computation and its evaluation schedule.

## Precise remaining case

An outer variable can occur in the original prepared record and disappear
from the normalized result. `normalization_can_erase_outer_dependency`
checks a concrete source smart-constructor fragment by kernel evaluation.
The original edge contains the outer argument and another reference.
Replacing the other child with `EmptyNode` makes `makeNode` discard the
entire edge. The normalized result contains no outer reference, although
the original record did.

This example shows that absence from the resulting probes does not imply
absence from the original memo key's free-variable set. It is a component
example for prepared substitution. It does not show that the full closed-input
construction reaches this case, causes a pending-key collision, or diverges.
No such source defect was established.

The remaining proof must handle this normalized-erasure case, or derive why
the supported closed-input environment cannot reach it. A general proof
needs exact structural substitution correspondence for both normalized
probe records, not only language equivalence. It must then connect that
correspondence to a completed earlier cache request.

Ordinary permutation equivariance alone is insufficient as a proof rule:
substitution of a fresh outer reference by `RecDepth` can identify it with
a nested depth probe's sentinel. This is not an injective renaming. The two
stored probes address such source distinctions, but their complete joint
correspondence has not yet been derived for arbitrary nested templates.

The proof uses the unbounded ordinal identity model from `Cache`. Its source
machine-word freshness condition remains the finite lifetime condition in
`InternedIdentityWords`; no unlimited `Int` freshness claim is added.

Validation on 2026-10-12: `lake build MicroCFTA.InternedFreshProbeKeys`
passes with 108 jobs. All 24 theorem axiom checks use only `propext` and
`Quot.sound`, or no axioms. No Haskell changes or Cabal runs were added.
