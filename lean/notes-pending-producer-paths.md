# Ordinary producers retain their actual source paths

Updated: 2026-10-13 15:47 CEST.

`InternedOrdinaryProducerPaths.Inputs` strengthens the callback-only input
invariant. Each ordinary capture retains an actual `Crossing` that introduced
the name. It also retains a `Path` from that crossing's body to the current
source expression. Each crossed callback retains its order in the cache
history.

`Inputs.producer` derives all of these facts for a captured `Unint level`:

- The producer's completed Depth callback returns that exact level.
- Its ordinary entry starts immediately after that callback.
- The current environment equals the crossed-name prefix followed by
  `Unint level :: producer.names`.
- The producer's captured environment is strictly shorter.
- The producer callback finishes before the current state.
- Every crossing on the source path lies between those states.

`InternedPendingProducerPaths.closed_encounter` derives the stronger invariant
at the actual active ancestor of any hypothetical closed pending execution.
The proof follows the same nested evaluator as the earlier origin proof.
It preserves paths through ordered node children, union operands, all three
binder callback entries, and cache effects. The theorem has no supplied
provenance premise.

`InternedPendingProducerReplay.closed_joint_mismatch` keeps this invariant
attached to the same `Site` and `Mismatch` as the joint-key extraction.
The current Depth and ordinary results are still the exact two original
ancestor records. The earlier completed pair and indexed live mismatch
remain present.

`producer_representative` uses the producer's actual completed Depth call.
It descends through the same source bodies and probe choices as the later
ordinary-entry route. This yields an earlier completed occurrence of the
target expression. It does not assume another execution of the producer.

`earlier_ancestor` applies this result to the active ancestor binder. It
derives an earlier completed execution of that binder inside the producer's
Depth call. That execution completes both probes and the request. Its
record is present before the active ancestor's reservation cut. Its key
therefore differs in at least one component from the active ancestor key.
The chronology is:

```
producer.before -> earlier binder start -> earlier binder finish
                -> producer.start -> origin.before -> origin.cut
```

The arrows denote the proved `Grows` relation. They do not assert strict
allocation or literal equality of intermediate caches.

This closes the missing source-path prerequisite described in
`notes-pending-producer-descent.md`. It does not prove paired-key mismatch
descent to two executions of the shorter producer. In particular, the new
earlier ancestor pair can differ from the original ancestor pair without
either producer-level equality being available. General closed constructor
no-pending remains open. All existing alias and pair fixtures remain intact.

Validation: the three new modules build with the pinned Lean toolchain.
The focused audit checks 9,264 theorem dependencies and permits only
`propext`, `Classical.choice`, and `Quot.sound`.
The log is `/tmp/mcfta-producer-path-audit.log`.
