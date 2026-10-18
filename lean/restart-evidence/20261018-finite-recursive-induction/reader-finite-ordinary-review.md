# Finite ordinary source step

Reviewed at 2026-10-18T09:26:44.889702+00:00.

## Selected source

`lean/MicroCFTA/SourceCurrentReaderFiniteOrdinaryStep.lean`
SHA-256 `8a0ad705c60eef2ce37e3bd7fd7e376dd8d208e83518ba61882c55b438982b3e`.

The four public declarations are `RelatedAt`, `AlignedAt`, `reference`, and
`ordinary`. `RelatedAt depth reader` retains physical Empty agreement and
`Same depth reader` for singleton roots. The reader is fixed.

`ordinary` derives `RelatedAt (depth + 1) reader` from actual warm raw node
calls, actual warm stored calls, initial Ready, available lexical inputs,
available replacements, and generic paired slots at `RelatedAt depth reader`.
The child hypothesis is indexed by an actual source row lookup and an actual
ordered child lookup. The proof derives the strict syntax-size bound at each
use. The hypothesis applies only to these strict source children. It does
not assume the relation for the whole parent or for a selected writer result.
Children can contain arbitrary nested Mu syntax.

The proof replays actual source and stored child calls at the same reader.
It retains complete symbols and guards. Both reconstruction stages account
for canonical row filtering. Child Empty agreement derives row survival.
Child finite observations derive ordered child matching one level deeper.
Closed node shortcuts use the existing physical node expansion; the proof
does not assume that Ready implies a canonical original row list.

The private symbolic-input proof uses reference shape and exact opaque
captures. It does not require equal resolved values in reference slots.
Opaque captures retain the same value and equal maps on their free names.
The `reference` endpoint consumes the generic slot relation directly.

## Boundary

This is a general ordinary-source induction step. It does not close the
binder or chronological selected-writer case. `AlignedAt` is a proper
strict-child induction hypothesis. It is not an unconditional source theorem.
The actual parent calls are observed warm calls at the fixed reader.
The endpoint does not construct a new reader or transport observations along
heap growth. It does not assume all-depth related self replacements.
No BinderFree, noDeep, finite Cap, or whole-heap closure premise is added.
No new constructed scenario was required by the parent task. Existing
source-built replacement fixtures are not recounted as new validation here.

## Validation

Selected strict: `reader-finite-ordinary-direct-2`; exit 0 and actual log size 0.
Selected canonical: `reader-finite-ordinary-canonical-1`; exit 0, 590 jobs.
Selected full imported probe: `reader-finite-ordinary-public-1`; four public pairs.
All eight options are explicit. Every pair contains `#check @`, full `#print`,
and `#print axioms`. The output has no omission or printer failure.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

Every selected worker records actual memory.max=4294967296,
memory.high=4294967296, and memory.swap.max=0 before running Lean.
The wrapper uses the pinned Lean 4.34.1 toolchain and a five-minute timeout.
Each attempt has an immutable executed source, raw log, metadata, and limits.
The owned peak file is separate from the root peak file.

Attempt direct-1 is retained. It failed on explicit application arguments,
a tactic-line layout, and an untyped source-row binder. Direct-2 corrected
these elaboration issues. It did not strengthen the mathematical premises.
No old source or old evidence was changed.
