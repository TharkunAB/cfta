# Initial causal payload mass and actual constructor review

Reviewed: 2026-10-17 06:31 CEST.

The two additive modules are `InternedValueMassHeap.lean` (149 lines, SHA256 `7505bb38a993efb0bdb48cd772a2ace9a9054c33f1e1050acbf1bc8a51242c19`) and `InternedValueMassConstructors.lean` (188 lines, SHA256 `3051a422e70b9d49fb8c3b38a9af326885ed87ec2400c803647b0c2b7a1dfba5`). They use the frozen `InternedValueMass` structural metric. This metric counts value, edge, and list constructors. A Mu includes its stored body and both probes. Keys, identities, symbols, guards, free-name fields, and cached depth do not contribute. Mass is not bytes, instructions, or allocation requests.

## Initial producer and store law

`Stored bound state` has three fields. `positive` bounds unit-mass Empty and reference values. `nodes` bounds every actual complete node payload at its key. `edges` bounds every actual complete edge payload at its key. Pending identity entries need no payload. The law covers both maps throughout construction, rather than only returned cells.

`initialBound source` is one plus the sum of actual node payload masses and actual edge payload masses. Both payload lists come from `SourceRecursiveIntersectionSourceProfile`. They read successful initial issued keys below the respective counters. `initial source facts` derives the store law. For an arbitrary node record, coherent canonical readback supplies its actual issued identity and key. For an arbitrary edge record, coherence first identifies the edge's own key, then supplies its issued read. Numeric range membership alone does not supply a payload. No future result-size or supply premise occurs in this producer.

`available` derives the bound for every available source value. `resident` derives it for an actual edge record. Empty and reference use `positive`; the other constructors use their own stored payload. The result admits recursive Mu, explicit union, and references. It has no ordinary-only or guard restriction.

`Stored.mono` increases the common bound. Cache-only updates preserve it. `put_node` and `put_edge` inspect the exact keep-first update. An earlier winner uses its existing causal bound. A fresh candidate uses its own derived bound. The actual `node_step` and `edge_step` helpers read that same current winner after insertion. They do not transfer a losing candidate's size to an earlier winner.

## Literal primitive producers

The `edge`, `node`, and `union` endpoints take only their literal inputs, current heap, and existing `Stored` law. They return the bound for both actual maps and the exact returned payload. Edge and union use `max oldBound (1 + values input)`. Node uses `max oldBound (1 + edges rows)`. No desired output law, availability, semantic answer, or future callback premise is required.

The weighted canonical row proof uses actual membership and absence of duplicate output rows. It bounds both list length and the sum of row masses. Dead-row filtering cannot increase mass. Union flattening and first-identity deduplication cannot increase value-list mass. The ordinary union path copies only existing row payloads. These facts cover both literal union branches.

`cleanup_le` proves that pure smart cleanup cannot increase payload mass. `filter` proves that actual root self-reference normalization preserves the SAME store bound when the input already fits that bound. A filtered union candidate fits the original union's mass. An earlier winner already fits the same store bound. No extra unit of slack is required.

These primitive bounds do not assert the physical validity of arbitrary user-provided records. The initial producer establishes the size law from legitimate source facts. Existing physical proofs can be composed separately at the same returned heaps.

## Validation

Both final strict source checks exited 0 with zero-byte output: `heap-mass-direct-3.log` and `mass-constructors-direct-3.log`. Canonical copies are `heap-mass-canonical.log` (1176 jobs) and `mass-constructors-canonical.log` (1179 jobs, combined with the separate encoding-width target). Both builds completed successfully. Their only warning is the inherited `InternedFreshOrdinaryClosedCompletion.lean:24` unused-input warning.

`heap-mass-public-1.log` contains 27 full explicit axiom/signature pairs. This includes the Stored type, constructor, and three fields. `heap-mass-kernels-2.log` contains two integration pairs. Final imported logs contain no warning, error, truncation, or `sorryAx`. Axiom dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`.

The first kernel constructs its own recursive Mu and explicit union from Empty. It derives the initial causal mass store. It then executes an edge with two copies of the actual root and a node with two copies of that actual edge. It derives both returned store bounds. It also proves exact whole-state warm reuse of that node request. The second kernel constructs a union with an added direct reference and the same actual source root. Actual normalization returns the original root at the exact current heap. It retains the same produced mass bound.

All failed source and kernel attempts remain as separate raw files. Early constructor attempts failed on syntax or unavailable helper names. The final proofs do not contain placeholders. No older proof source, Haskell source, or frozen evidence file was changed.

## Remaining boundary

This component supplies the causal initial store and actual local constructor bounds. The separate full Fresh result-size producer handles recursive callbacks, all actual intermediate heaps, the three Mu payload fields, and the current keep-first winner. A full native static constructor budget must also bound generated callback syntax and the number of recursive requests. This component does not prove that budget, signed host capacity, full query completion, or runtime correspondence. No new Haskell behavior defect was found.
