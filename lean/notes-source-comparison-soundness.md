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

`MicroCFTA/MergedComparisonPreparedSoundness.lean` now proves the required
prepared-cache semantic inclusion. `check_sound` transfers every finite
epsilon-accepted term from the narrow operand to the wide operand after a
successful true comparison with an empty initial ancestor list. It requires
`Facts`, `Prepared`, `Ready`, available closed operands, and a sound
interpretation of guards marked clear. No semantic callback law remains.

The proof derives complete child, cover, and row certificates. Induction on
finite-term height justifies numeric ancestor reuse. Coherence proves that
each closed numeric identity determines the complete original record.
The module builds with 245 jobs. `check_bounded` and `check_sound` use only
the three standard axioms. The audit is
`/tmp/mcfta-comparison-prepared-soundness-axioms-20261013.log`.

`MicroCFTA/MergedComparisonSoundness.lean` closes the actual-cache boundary.
`check_sound` proves finite-term inclusion in the actual returned cache.
`check_later_sound` proves the same inclusion in any later cache with
`Facts`, `Prepared`, and both retained available operands. Neither theorem
requires `Ready` or a warmup.

The proof first replays the completed comparison in the chosen cache.
`check_fixed_sound` proves soundness for that cache-preserving execution.
Every verified changing prefix warms a previously cold recursive record.
Such a prefix cannot grow back to its starting cache. The exact verified
suffix supplies that growth, so all demanded intermediate caches equal the
chosen cache. This argument includes unsuccessful cover candidates.

The same finite-term height induction then discharges all recursive calls
and numeric ancestor reuse. No recursive callback, semantic coinduction,
or termination premise remains in the three soundness theorems. The full
guard interpretation and the soundness of the supplied clear-guard test
remain explicit. Inputs must be closed and available in the original
`Facts` and `Prepared` cache. The proven stored-body preparation fragment
is unchanged.

The actual-cache module builds with 248 jobs. `check_bounded`,
`check_fixed_sound`, `check_later_sound`, and `check_sound` use only
`propext`, `Classical.choice`, and `Quot.sound`. The audit is
`/tmp/mcfta-comparison-soundness-axioms-20261013.log`.
