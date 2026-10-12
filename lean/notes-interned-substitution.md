# Recursive substitution through nested rebuilt binders

`InternedSubstitution` removes the closed-external-environment restriction
from the recursive induction. `run_exact` proves capture-avoiding semantic
substitution for every finite input shape and every replacement environment.
The environment can contain fresh outer `Rec` references. No binder language
equivalence, successful fuel run, or replacement-closedness premise is needed.

`run` follows the prepared substitution branches. A closed shape is returned
unchanged. A reference reads its replacement once and does not traverse the
inserted value. Constructor and union children retain their order. At a
binder, the worker restricts the external environment to that binder's free
references, overrides the old local reference, recursively rebuilds the body,
removes its bare self-reference from root alternatives, and applies the two
`createMu` cleanup cases. Unlike the earlier one-binder
adapter, nested body plans execute the same recursive worker.

## Finite allocation

`replacementNames` reads free references from only the replacements that the
current binder can use. `allocate` selects a name above the input supply and
every name in the original body and those replacements. `allocate_fresh`
derives capture avoidance. It includes open replacements such as the fresh
outer reference inserted by an enclosing binder.

The worker passes the supply through children in their original order. Each
binder advances the supply before it visits its body. `run_supply` proves
that the returned supply cannot decrease. `issued` records the actual fresh
names selected by these calls. `issued_range` puts every recorded name between
the input and returned supplies. `issued_distinct` proves that nested binders
and separate child plans never receive the same newly allocated name in one
execution. All of these traversals terminate on the original finite syntax.

This is an explicit finite allocation witness for alpha-renaming. It is not
the runtime interning counter or a proposed Haskell change. The source can
reuse an existing binder on a canonical cache hit. `allocation_independent`
proves that the initial witness counter cannot change the resulting language;
it does not equate the resulting identities. Finite machine allocation limits
remain in `InternedIdentityWords`.

## Exact language and closed unfolding

The main induction compares each rebuilt body under its new local language
with the original body under its old local language. `local_semantics`
derives that equality from actual environment lookups and the computed
capture-avoidance condition. The binder case then uses least-language
congruence, the root-union language law, and the proved cleanup equations.
`BinderSelfUnion.binder_free_exact` proves that the filter also preserves the
complete free-reference list after binding. It makes no recursive assumption
that outer replacement references are closed.

`run_free` proves that the result introduces no free name beyond the names
allowed by its original references and their actual replacements.
`run_closed` specializes this result to a resolved closed environment.
`run_lexical` identifies the full worker's language with lexical substitution
when the original external replacements are closed. `run_exposed` gives the
exact visited constructor-row language, and `run_no_unexpected_reference`
excludes a later raw-reference request.

`unfoldRebuilt` runs this worker on a binder body with the binder itself as the
replacement. `unfoldRebuilt_exact` derives the original least language even
for an open binder. For a closed binder, `unfoldRebuilt_closed` derives a
closed result. `unfoldRebuilt_exposed` and `unfoldRebuilt_bounded` then prove
exact epsilon exposure and constructor-height bounds. These theorems cover
arbitrary nested binders and references from an inner binder to an outer one.
`open_replacement_not_captured` also checks a concrete collision between an
old nested binder name and an inserted free reference.

## Remaining source representation boundary

The worker is the pure recursive binder algorithm over lexical shapes. It
retains constructor payloads and ordered child lists. It does not execute
the mutable plan cache, binder-result memo cache, or two-probe hash-consing
protocol. Ordinary edge sorting, deduplication, and empty-child cleanup keep
their existing constructor adapters. Connecting all those runtime results
to this worker remains necessary for full source readback.

In particular, this result does not establish a finite image of runtime node
identities under repeated unfolding. Runtime cache reuse must implement a
stable representation of these alpha-equivalent results. Language equality
and finite allocation in one worker call do not prove that property. The
`LexicalBoundedBuilder.RowsCorrespond` representation interface remains open.

Validation on 2026-10-12: the pinned toolchain builds
`MicroCFTA.InternedSubstitution` and its dependencies (77 jobs). The theorem
audit uses only standard Lean axioms. No axioms, incomplete proofs, or Haskell
changes were added.
