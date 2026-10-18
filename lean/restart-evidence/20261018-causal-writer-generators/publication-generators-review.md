# Publication reconstruction generators

Reviewed at 2026-10-18 21:44 CEST.

The production source is `lean/MicroCFTA/SourceCurrentPublicationReconstructionGenerators.lean`.
Its SHA256 is `659fe8b43384b664db84938f12936575807f35ab7c91ba292da7bc94b28e5e2f`.
The sole public theorem is `publication` at line 142.

The theorem consumes an actual selected `Publication` event.
It takes one Ready reader and forward `Grows event.after reader`.
The actual candidate must be Available at that reader.
The common outer Environment must satisfy Replacements there.
The common local replacement must also be Available there.
Both actual stored calls must return at that same reader.
The body map binds the reserved interned name to the local replacement.
The ordinary map binds the actual ordinary marker to the same replacement.
The theorem derives `Generated reader left right` and its reverse.

The proof generalizes the frozen private `publication_generated` in
`SourceCurrentRetainedMuDirectedCase.lean` at line 196.
It retains the actual raw source callback states and adjacent root-filter calls.
It derives both historical lexical Contexts from the event.
It replays the raw source calls and root filters at the final reader.
The candidate availability premise supplies availability of the actual body and ordinary values.
The sparse shared map retains the outer Environment outside the two local names.
Its replacement proof handles the outer branch explicitly at lines 71 to 82.
The lexical captures use the same shared map on both sides.
They therefore require no extra capture freshness premise.
The existing actual publication freshness proof supplies the live alias and self-test facts.
Both Generated.filtered constructors retain the exact call order and filter endpoints.

This result does not consume a semantic law, BodyIH, Directed premise, or assumed output comparison.
It permits open captures, arbitrary nested Mu source forms, unions, and either Empty outcome.
It does not prove Same, Related, a language law, or reader observation transport.
It does not construct a later reader or derive an event from History.
The root component owns selected-writer Path recovery and actual call preparation.
History alone cannot replace the explicit growth premise: a History retain constructor does not preserve all four tables.

Selected evidence:

- `publication-generators-direct-1`: exit 0; actual strict log size is 0 bytes.
- `publication-generators-canonical-1`: exit 0; clean build with 600 jobs.
- `publication-generators-public-1`: exit 0; one full public signature, proof, and axiom report.

Every selected Lean job uses Lean 4.34.1, a four GiB max and high limit, zero swap, and a five-minute cap.
The public probe enables all eight required options and contains no printer omissions.
Its axiom set is a subset of propext, Classical.choice, and Quot.sound.
This component owns one new public pair, zero constructed pairs, and zero auxiliary pairs.
There are no failed or unselected attempts.
The explicit manifest excludes root scripts, root peaks, shared selections, and mutable fixture work.
