# 7. The completion of a law stops at a fuel of critical pairs and keeps its rules

## Context

Specftacular completes the rules of each new law. A completion that
allocates more than its budget (256 GiB) keeps only the rules of the law
alone, and its work is lost. At HugeLists 7-p4 with the matrix flags, 78 of
the 609 completions over 1 GiB ran over the budget. They took 76 % of the
time of the completion and about 41 % of the 14,081 seconds of the run. Most
of them complete laws of the list monad, for example
`xs >>= f == concat (map f xs)`.

## Decision

The completion of a law takes at most 2^15 = 32768 critical pairs from its
queue (`--completion-fuel 15`; 0 is no limit). When the fuel runs out, the
law keeps the rules that its completion has derived. The allocation budget
stays as a second limit.

## Why

- The rules of a stopped completion follow from the laws, so they are
  sound. They prune more than the rules of the law alone.
- A count of pairs does not depend on the allocation, so it gives the same
  laws with each optimization and each number of capabilities. The
  allocation budget does not.
- A pair costs about 1 MiB at HugeLists, so the fuel stops a completion at
  about 32 GiB. HugeLists 6-p4 gives the same output in 486 seconds against
  577. HugeLists 7-p4 runs in 6,381 seconds against 14,081 under the load of
  other jobs (5,800 seconds on a quiet host with 30,000 pairs), and it
  allocates 27.3 TB against 61 TB. Each one-core configuration of the
  comparison with Spectacular gives the same output.

## Consequences

- The laws change where a completion runs out of its fuel. At 7-p4 with
  `--enumerate-ahead`, 578 laws of the earlier run are not printed: the
  rules of the stopped completions prove them. 45 other laws are printed: a
  stopped completion does not derive them. At 7-p3, 11 laws are added. Each
  printed law passes the tests and the rechecks.
- A fuel of 30,000 pairs gave Regex 7-p4 one more law: the completion of
  the AC law of `|` needs more pairs. 2^15 pairs are enough for it.
- Some completions still run over the budget within the fuel: at 7-p4,
  three laws over `[[[A]]]` cost more than 8 MiB for each pair.

## Discussion points

- A lower allocation budget: it also stops the long completions, but a law
  over the budget keeps only its own rules, and the allocation of a
  completion changes with each optimization.
- Speculative completion, which decides the next critical pairs in
  parallel sparks: the decisions are the same, but with lazy blackholing the
  main thread does the work again, and with eager blackholing the run stopped
  making progress.
- Twee has a similar limit: `cfg_max_critical_pairs` in twee-lib.
