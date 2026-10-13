# Exact completed cold-merge replay

`MergedColdMergeReplay.source_worker_replay` proves exact replay for every
successful pair of ordinary and comparison fuel bounds. Its premises are
`Facts`, `Prepared`, and input `Available` in the original cache, the actual
successful worker result, and `Grows` from that returned cache to a later
view. Replay returns the identical complete value and leaves the entire
later view unchanged.

`source_execute_replay` applies the same result to the source driver. It
reuses the original input's derived ordinary height and the original
comparison fuel. Both source theorems use actual source grouping. They
require no callback replay law, grouping law, `Ready` cache, initial warmup,
issued-reference extension, or facts about the later view as a separate
premise. The generic worker theorem permits any grouping that satisfies
the existing source grouping contract.

The proof follows the actual source sequence. Completed selection reruns
its successful and unsuccessful comparisons and returns the same retained
list. Retained columns replay their exact ordinary or recursive union
branch. Small edges replay each child. Large edges replay each column.
Groups retain the literal four-row threshold. The root replays its ordered
groups before its complete node request. Induction on ordinary fuel
discharges every recursive callback certificate. Completed source facts
are derived at the actual intermediate caches.

The source comparator has no memo table. Its replay theorem derives its
answers from retained immutable records. The complete worker result can
therefore support reuse by the outer merge memo on this modeled ordinary
fragment. This result does not add a source memo or prove an arbitrary
external memo implementation. It proves successful recomputation has the
same exact output and no further effects.

The theorem is conditional on a completed original run. The separate cold
merge completion theorem supplies such runs in the prepared fragment.
The original `Prepared` condition excludes open nested Mu reconstruction
in stored unfolding. The proof keeps that boundary explicit.

The pinned Lean 4.34.1 build passed for `MergedColdMergeReplay`. The isolated
axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
Its temporary driver is /tmp/mcfta-cold-merge-replay-audit.lean.
