# Distinct used Mu replacements at one actual reader

Frozen at 2026-10-18 11:10 CEST. This evidence-only component contains one constructed theorem, `MicroCFTA.ReaderReplacementKernels.distinct_used_replacements`. It changes no production source.

## Source and physical witnesses

The first source is the raw binder `mu x. f[x]`. The second is the raw binder `mu y. f[f[y]]`. The symbol and complete guard of every unary row are zero and `false`. The fixture constructs the two actual `Publication` values in source order. The first starts at empty. The second starts at the first publication's exact returned heap. The second joint source context follows from `Context.build` and the first actual source equation. Both events retain their literal Depth, ordinary, and reserved-body callbacks and their actual missing keys.

One closed root source contains these two sources and the three ordinary sources `f[first]`, `f[second]`, and `f[f[second]]`. Repeated binder construction uses the canonical cached values. The actual root completion derives `Ready` at its returned reader. The public theorem retains source child positions zero and one, both exact installed full Mu records, both values' availability, inequality of the complete values, inequality of their keys, and `usesLocal=true` for both. The two replacements are distinct actual source-built Mu values.

The last three source children preallocate the ordinary unfolding results. Literal repaired execution proves that the first Mu unfolds to `f[first]` and the second unfolds to `f[f[second]]` at the same reader without changing its complete heap.

## Derived reader-relative relation

The relation is proved from these actual unfold equations. It is not an input. For every observation depth `n`, the proof derives two statements together:

- `Same n reader [first] [second]`.
- `Same n reader [first] [f[second]]`.

At depth zero, the ordinary unfolding results expose no bare references. At the next depth, the first statement uses the second statement at the smaller depth to match the unary child. The second statement uses the first statement at the smaller depth. Actual node rows retain the exact symbol and full guard. Backward matching uses the symmetric child relation. `OpenObservations.unfold` composes the ordinary row observations with each actual Mu unfolding.

Both values are physically nonempty Mu records. This proves `ReaderObservations.Related reader first second`: physical-empty agreement and `Same` at every finite depth in this fixed reader. It does not prove the relation in arbitrary heaps or after arbitrary reader growth. The unary cycles have no finite accepted-tree witness in this component. No finite inhabitation claim is made.

## Actual replacement consumers

The generic `ReaderReplacementSlots.publication_extend` is instantiated with `relation := ReaderObservations.Related reader`. Its initial capture lists are the actual empty capture lists of these two publications. It binds the first publication's self name to the first Mu and the second publication's self name to the distinct second Mu. The resulting ordered `Paired` evidence allows distinct related resolutions. The theorem also derives both literal raw reserved-body calls, both actual root filters, and the growth from each raw return to its own filtered body endpoint.

The public witness retains both actual `build (.var 0)` followed by repaired `execute` equations at the reader. They return the respective distinct Mu values and the exact same reader. `ReaderReplacementSlots.reference` consumes those equations, the derived `Paired` evidence, and source-derived coherence and reference availability. Its conclusion supplies the public reconstructed-result relation.

No caller-supplied output relation, future completion, binder congruence, desired callback alignment, or growth law is used. This is a concrete reader-relative replacement integration. It does not establish general retained-body/common-replacement alignment, full binder reconstruction congruence, or chronological selected-writer induction for arbitrary syntax.

## Selected checks

- Strict: `reader-replacements-kernels-direct-5`, terminal zero, actual zero-byte raw log.
- Strict source SHA256: `ad1968b131418b3c281960744ee825d27e3b419a1a3510fbd1d3e41cb58f1c8b`.
- Full group: `reader-replacements-kernels-public-1`, one constructed pair, zero production pairs, zero auxiliary pairs.
- Full source SHA256: `bb20c41d689e1628f1762166322e2fdaeb026a8f2e73dce41ca04a65f1a86ea4`.
- Full output has 71653 bytes. Hardened validation passes all eight explicit options, `#check @`, full proof printing, and axiom printing. No omissions, printer failures, warnings, errors, or `sorryAx` occur. Only standard axioms occur.
- Selected executions use pinned Lean 4.34.1, all linters, a five-minute cap, and effective cgroup `memory.max=4294967296`, `memory.high=4294967296`, `memory.swap.max=0`, read inside the worker.

Four failed attempts remain immutable. Prefix one had a local existential-binder syntax error. Prefix two had a backward row-match orientation error. Direct three needed an explicit ReaderObservations import after the generic Slot module removed that dependency, and equation unfolding for the literal variable calls. Direct four needed the fully qualified `bind` definition in its simp list. These were fixture elaboration errors. No resource termination or production defect is claimed. The final strict and full probes pass.

This evidence-only component has no independent canonical production target. The production owners supply canonical receipts. The explicit manifest pins final production source bytes and owned evidence only. It excludes mutable root files.

Final Slot source SHA256: `ab29b32220b1d6a77db19cdbebb78c9cd98881fe4c6d82439fea9adfb15f6780`.
