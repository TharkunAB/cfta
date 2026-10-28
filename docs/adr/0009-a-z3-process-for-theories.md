# 9. cfta starts a Z3 process for theories

## Context

A theory (ADR 0008) gives Z3 its datatypes and recursive definitions as
SMT-LIB text: `declare-datatypes` and `define-funs-rec`
(`Data.CFTA.Refinement.SmtLib`). The Z3 entailment of cfta goes through
Liquid Fixpoint, whose SMT interface prints `define-fun` only. It has no
`define-fun-rec`, no raw command, and no sequence theory, so it cannot state
a recursive definition. The SMT-LIB text needs a Z3 process that reads it
directly. A test can start one, but every user of a theory would have to
write the same process code.

## Decision

cfta starts the Z3 process itself, through `System.Process`.
`Data.CFTA.Refinement.Z3Process.withZ3Theory` starts one long-running `z3`
from `PATH` for each entailment value and sends it the commands of the
theory once. Each query runs between `push` and `pop`. The verdicts and the
time limit follow `withZ3Timeout`: `unsat` gives `Yes`, `sat` gives `No`,
`unknown` gives `Unknown`, and a check that takes the whole limit raises
`TimeLimitReached`. An error of Z3 raises an exception, and a new process
replaces the old one.

## Why

- Only a raw SMT-LIB path states recursive definitions. Liquid Fixpoint
  would need `define-fun-rec`, or cfta would have to unfold the definitions
  itself, as proof by logical evaluation does in Liquid Haskell.
- One process with `push` and `pop` sends the theory once. A process for
  each query spends about 12 ms on the start of Z3, more than the solver
  needs for a ground query.
- The same verdicts and time-limit policy as the Liquid Fixpoint entailment
  let a caller combine both through `fallback` and catch one exception.

## Consequences

- `process` becomes a direct dependency of `cfta`. It is a GHC boot package,
  and `liquid-fixpoint` already depends on it, so the build plan does not
  change.
- `z3` must be on `PATH`, as for the Liquid Fixpoint entailment. Without it,
  `withZ3Theory` raises the exception of `System.Process` when it starts.
- A theory with a datatype without values has no SMT-LIB text. Then each
  query gives `Unknown`, and no process starts.
- The entailment holds one process for the lifetime of the callback. Queries
  of one entailment run one at a time.

## Discussion points

- A process for each query: simpler, and no state between queries. It stays
  possible from the text of `entailmentScript`, and the tests compare both.
- Liquid Fixpoint's process with raw text: its `Command` type has no raw
  command, and it reads one answer for each command, so text that it did not
  write would shift its answers.
- Other solvers that read SMT-LIB 2.6, such as cvc5, could use the same text.
  This decision starts Z3 only.
