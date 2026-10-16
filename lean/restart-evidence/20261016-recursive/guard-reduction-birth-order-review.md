# Independent review: reduction birth-order component

Date: 2026-10-16 04:59 CEST. Read-only review. No proof/source edits or builds.
Reviewed source: lean/MicroCFTA/SourceCurrentReductionBirthOrder.lean.
SHA256: 704b0c1ee0824d1489388545117d9f3ccd181c77f34bddd3a4fb91616eb18432.
Compared with main d44b2a0f, cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:569-672.

## Result and wording limits

No concrete theorem defect or mismatch in the finite table equations was found. The module explicitly leaves source traversal, refold execution, runtime identities, native containers, Double conversion, and enumerator order as adapters. Its injective-renaming results are correctly described as finite observation correspondence, not whole process-history independence.

Two component/source differences must remain visible in summaries:

- Component births accepts an empty observed history and returns the empty table. Actual Synthesis.births [] throws `births: no space` (Synthesis.hs:649). No public orderedSpace totality statement for an empty history follows from these theorems.
- source_history_bound is a length theorem for reductions of a supplied total step function. It proves neither completion of the actual reducePartially/withoutRedundantEdges step nor pairwise distinct history values. The actual source can stop on adjacent equality or the fixed budget; it has no general cycle-detection rule. An alternating two-state step can have 31 history elements with only two distinct values. Exported orderedSpace accepts arbitrary supplied histories and has no fixed-31 length guarantee.

The module's current header retains component scope. A future source-facing completion statement must additionally discharge the actual completed step/traversal premises rather than treating the numeric round limit as whole reduction termination.

## First-wins rounds

Source Synthesis.hs:646-668 increments its Int round number once per supplied space, starting at zero. It visits nodes in depth-first edge/child order, skips Empty, and uses one node-identity seen set across every round. For a fresh visited node it inserts all outgoing edges with `IntMap.insertWith (\_ old -> old)`, then prepends ordered children to pending. Thus an existing birth is retained even when an edge is observed again in the same or a later round.

Component recordRound/birthsFrom at lines19-29 execute exactly this first-insert rule on supplied finite round key observations. recordRound_lookup/birthsFrom_lookup/births_exact prove independent earliest occurrence, rather than assuming it. Duplicates within a supplied round do not change the birth. The actual node traversal and its global seen optimization are not implemented here. Relating the observations to all source-reached edges still needs immutable complete node identity and actual traversal/readback. In particular, skipping a previously seen node is justified only when its identity retains the same outgoing edges.

## Refold collisions and original union

Actual orderedSpace (Synthesis.hs:628-639) computes mapped-edge entries only for final reachable edges whose OLD key has an original birth. It uses `IntMap.fromListWith min` for collisions among mapped keys. It then uses `IntMap.unionWith min born mapped`, with born literally the left table. This is minimum union, not left-biased union.

Component transportEntries (lines283-300) preserves the exact old-birth lookup and skips absent old births. fromMinEntries and foldMin (lines180-280) prove that colliding entries retain their minimum, including a genuine originating entry. rounds/minUnion (lines303-352) include both the original table and mapped-entry table and prove the least originating birth. The original left table does not override a smaller mapped birth. No hidden one-preimage or injective-refold assumption is introduced. The source min combiner is symmetric, so the component's old/new insertion argument order does not change these Nat results.

The proof does not establish that the supplied edge-key pairs are produced by actual refoldEdges, that every final edge has the expected observation, or that refold terminates. It does not equate constructor heaps or allocation schedules. Those source obligations remain explicit.

## Renaming and fallback

locateRound_rename/births_rename/fromMinEntries_rename require an injective key correspondence. rounds_rename additionally requires literal agreement of the old birth table on every mapped key. history_rounds_rename derives that agreement for a fully mapped finite history. These are the correct finite algebraic conditions. They do not produce the correspondence between two process executions, their histories, or their refold edge maps.

rounds_bound (lines417-422) is justified by actual original or transported origin: a known birth lies strictly below history.length. index_unknown and known_before_unknown use the same history.length as the fallback count. This matches the source count for a completed nonempty finite history starting at zero. It does not assert an arbitrary externally supplied fallback count exceeds all births.

Source birth indices/count are machine Int, while the component uses Nat. Native key identity capacity and counter conversion/no-overflow remain distinct adapters. For a completed normal reductions history the bound is at most31, so its round/count values fit the ordinary host Int and are exactly representable as finite Double values. Arbitrary public histories do not inherit that numeric bound; machine counter wrap and Double rounding cannot be omitted from a general source order theorem.

The source order is the NEGATIVE Double conversion of the index. Smaller known indices are heavier. The component proves Nat index comparison only. It does not prove that runsBy enumerates terms in the claimed canonical tie order or that larger weights map to a particular complete global proposal sequence. The module header correctly retains both numeric and enumerator adapters.

## No additional action requested

No proof edits are needed for this bounded component. Retain empty-history error behavior, total-step versus actual source completion, non-distinct histories, and public-history numeric limits when documenting the next source-facing composition.
