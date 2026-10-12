# Constructor-derived probe provenance

`InternedProbeProvenance`, `InternedTemplateProvenance`, and
`InternedConstructionProvenance` derive the residency and issued-reference
premises used by `InternedFreshProbeKeys`. They execute the existing source
constructor functions. They do not define a replacement cache algorithm.

`Available` states that a value is its resident canonical record, every
free interned reference has an earlier reservation, and all retained child
records have the same properties. Mu records include their stored body and
both probes. `Cached` applies this invariant to the actual edge and node
record tables. Empty tables satisfy it directly.

`nodeStep_available` and `edgeStep_available` prove preservation through
first-writer readback. The returned record can be an earlier canonical
payload. The proof therefore checks the complete stored records, rather
than assuming that readback returns the newly supplied candidate.
`makeNode_available` covers empty-child removal and canonical edge sorting.
`makeUnion_available` covers flattening, identity deduplication, and the
ordinary-node fast path.

`compile_available` composes these laws through the actual template syntax.
The only supplied value premises concern its original argument and captured
records. `compileBody_available` includes `withoutSelfReference` before
each probe. `probes_available` runs the depth probe and then the ordinary
probe at the first probe's recorded depth. It derives both probes'
residency and issued-reference provenance in the returned state.

`finishMu_available` covers the real cache hit and miss branches. The miss
reserves the binder identity, makes that exact recursive reference
available, runs the normalized body, and completes the canonical Mu
record. `createMu_available` also covers removal of an unused binder and
the bare self-cycle.

`SourceBuilt` is an empty-cache trace of the existing ordinary and smart
Mu constructors. At each step, it requires provenance only for the finite
original inputs. `sourceBuilt_constructed` embeds it into the older
`Constructed` trace. `sourceBuilt_correct` derives record coherence,
complete payload coverage, and reference provenance. The older trace
alone cannot establish the last property: it permits arbitrary captured
records and arbitrary reference arguments.

`nested_probes_separate` evaluates the actual outer probes, reserves their
key, and evaluates the inner probes in that state. If either inner probe
retains the fresh outer reference, its two-probe key differs from the
pending outer key. No probe residency or probe provenance premise remains.
The theorem still requires provenance of the inner template's original
captured inputs. `nested_example` discharges that premise from the actual
outer reservation and checks a fresh-dependent nested construction.

The retained-reference condition remains explicit. This work does not
settle the normalized-erasure case documented in
[the fresh-key notes](notes-interned-fresh-probe-keys.md). It also does not
prove that every independent inner binder request completes during the
outer probe schedule. Templates execute finite ordinary constructors and
can capture earlier complete Mu records. A compiler for arbitrary dynamic
nested Mu callbacks remains a separate source adapter. Machine-word
freshness and lazy evaluation remain separate from the unbounded finite
constructor model.

Validation uses pinned Lean 4.34.1. The construction module builds in 111
jobs. The isolated dependency audit permits only `propext`,
`Classical.choice`, and `Quot.sound`. No Haskell source changed.
