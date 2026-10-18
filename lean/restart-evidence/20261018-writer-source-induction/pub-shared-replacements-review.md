# Shared replacements at actual publications

Recorded: 2026-10-18 11:43 CEST.

The source is `SourceCurrentPublicationSharedReplacements.lean`.
Its SHA256 is `ae6f65e3f0627850fa4a0a2e635b492e7f85003c03b2f23a36b83036829b0b09`.
The module has four public declarations: `shared`, `cross_absence`,
`substitutions`, and `paired`.

## Produced facts

Let q be the actual reserved interned name. Let r be the ordinary name
selected from the actual Depth callback. `cross_absence` derives r absent
from the actual filtered body and q absent from the actual ordinary value.
It uses both directions of `UsedBinderAliasTransport.publication_filtered`.
The two names have different Reference constructors. The proof does not
assume that either name is absent from every fixed capture.

The shared sparse map binds q to the first replacement and r to the second
replacement. It retains the original map elsewhere. `substitutions` proves
that each original sparse substitution has the exact same complete
execution outcome as this shared map at the supplied heap. The theorem
requires that heap to be Coherent and both original callback values to be
Available. It requires no future completion equation or output comparison.
The replacement values can differ. No replacement availability is needed
for this equality of complete execution functions.

`paired` uses the SAME shared map for both actual lexical input lists.
The leading references resolve to the two supplied related values. Every
fixed capture has equal maps on all its free names. Reflexivity handles
reference captures. This proof needs no all-capture freshness premise.
The relation is generic. A consumer can use a finite relation at one fixed
reader without moving observations to another heap.

The actual Publication is a causal record of completed source callbacks.
A caller can obtain it from the existing source history producers. This
module does not construct a new Publication or assume a desired callback
result law. It does not compare completed binder outputs, produce an
older-winner relation, or establish a general Mu weak simulation instance.
There is no BinderFree, Cap, closedness, or source-root restriction.

## Checks and retained attempts

Selected strict check: `pub-shared-replacements-direct-2`. Its exit code
is zero and its literal log length is zero bytes. The canonical build
`pub-shared-replacements-canonical-1` completes all 592 jobs without a
warning. Selected `pub-shared-replacements-public-1` checks all four full
signatures, definitions or proofs, and axiom reports. It uses all eight
required options. The hardened checker rejects omitted proof text and
printer failures. It accepts only propext, Classical.choice and Quot.sound.
The full raw public log has 152325 bytes.

Attempt direct-1 failed because the unqualified `bind` in simp was
ambiguous. The correction qualifies the existing sparse binding definition.
The failed immutable source, metadata, log and effective limits remain.
All four jobs record effective MemoryMax=4294967296,
MemoryHigh=4294967296, and MemorySwapMax=0. Each job uses the heavy-management
five-minute cap and pinned Lean 4.34.1. The task uses its own peak log.

Counts: four new public pairs, zero constructed pairs, zero auxiliary pairs.
The parent owns any actual writer integration. No shared mutable fixture,
selection, or global authority file is pinned by this component.
