# 8. The completion decides its critical pairs in parallel threads, inside a pure `addLaw`

## Context

On 12 cores, the completion of each law ran on the thread that tests, and
the other capabilities waited. At HugeLists 7-p4, the completions took
1,038 of the 3,996 seconds. Sparks did not help: with lazy blackholing, the
main thread did the work of a spark again, and with eager blackholing, the
run stopped making progress.

## Decision

With `--speculate N`, the completion decides up to N critical pairs of its
queue in `forkIO` threads, under the rules of the moment, and takes the
decisions in order. A new equation sends the pairs after it back to the
queue. The number of pairs in parallel doubles, up to N, after a step
without a new equation, and it becomes k + 1 after a new equation at
position k. The threads run in `unsafePerformIO`, so `addLaw` keeps its
pure type. The allocation of the decisions that the completion uses counts
against its budget. The flag is off by default.

## Why

- A decision is a pure function of the pair and the rules, so the
  decisions are the same as on one thread, and the result is
  deterministic. The `IO` stays in one function, and the callers of
  `addLaw` do not change.
- The main thread waits on an `MVar` for each result, so it never does the
  work of a thread again.
- A fixed window of 64 took 4,659 seconds at 7-p4: in the large
  completions, a new equation came every few pairs and discarded most of
  each batch. The adaptive window takes 3,583 seconds.

## Consequences

- The allocation is 6 to 11 % higher at HugeLists 6-p4 and 7-p4, because
  the decisions after a new equation are made again.
- The threads have no cache of normal forms, so a completion counts more
  allocation against its budget. At 7-p4, five completions run over it
  against three. The output does not change there, but near the budget a
  completion can keep only the rules of its law and give other laws. The
  fuel (ADR 7) gives the same laws with each number of capabilities; the
  budget does not.
- With one capability, the flag only costs time.

## Discussion points

- Make the completion an `IO` action. `boundedCompletion` already runs it
  in `IO`. This is more explicit, but it changes the type of `addLaw` and
  of its callers.
- Count all the allocation of the threads, also that of the discarded
  decisions. The budget is then stricter, and further from the count on
  one thread.
