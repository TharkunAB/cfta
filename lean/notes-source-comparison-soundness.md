# Common-cache replay for ordered source comparison

`MicroCFTA/MergedComparisonSoundnessReplay.lean` compiles with Lean 4.34.1.
Its namespace is `MicroCFTA.MergedComparisonReplay`. The targeted build
includes 183 jobs.

`check_replay` takes an actual completed ordered comparison. The original
cache must have `Facts` and `Prepared`. Both operands must be available and
closed. For every extension of the actual final cache, the same fuel and
numeric ancestor stack return the same Boolean. The replay returns the
later cache unchanged. No callback law or later preparation premise remains.

The proof follows the actual child order, cover search, and demanded reads.
It includes the effects of unsuccessful cover candidates. Each earlier
reader replays after all later effects. It never assumes that the original
execution used a prepared observation cache.

`check_observation` prepares the actual final cache once. It derives a
common observation with `Facts`, `Prepared`, retained warmup outputs,
`Ready`, and both original available operands. The full ordered comparison
replays there with the original Boolean and no effects.

The two theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
The audit is `/tmp/mcfta-comparison-replay-axioms-20261013.log`.

This result supplies exact common-cache replay. Semantic inclusion still
requires the prepared-cache successful-comparison certificate and numeric
ancestor-pair interpretation. The reader coverage theorem supplies exact
constructor-edge language in that cache. The existing finite-term
`Checked` theorem can then discharge ancestor reuse. Replay alone does not
claim this semantic inclusion.
