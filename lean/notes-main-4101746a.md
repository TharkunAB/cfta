# Main 4101746a source refresh

Main `4101746a` is merged at `0fca52f8`.
The refresh changes twelve source, test, and package files.
The equality, interned constructor, and Sized implementations are unchanged.
All earlier proofs, counterexamples, repairs, and marked drafts remain.

## Conjunction-based emptiness

`Enumeration.provablyEmpty` now explores conjunctions of resident nodes.
It does not construct intersections of recursive requirements.
The source combines matching-symbol, matching-arity edge tuples.
It then builds child-column and equality-class projection conjunctions.
The budget counts admitted conjunction identity lists.
Open and unadmitted requirements remain possible.

`SourceCurrentConjunctionEmptinessRows` retains the literal edge-tuple fold.
Its tuple components follow the tail operands, then the original head.
The proof derives tuple coverage from individual accepted-node exposure.
It derives combined equality satisfaction and smaller accepted requirements.
No complete tuple-row soundness oracle is supplied.

`SourceCurrentConjunctionEmptinessTable` proves finite worklist exploration,
retained stored reads, the admission bound, and finite fixed-point soundness.
Its literal canAccept and source growth step agree with the finite carrier.
Completed node exposure, path readback, and faithful closed resident keys
remain explicit adapters. Exact IntMap last-winner readback, concrete
containers, and lazy runtime execution remain open.
Earlier emptiness proofs retain their historical source definitions.

## Solver declarations

The solver now declares the fixed scope once when it creates a process.
Each query bracket declares only its fresh and inferred undeclared names.
Context replacement creates a new process and declares the fixed scope again.
`SourceSolverDeclareOnce` follows that command sequence and retains the
current query-preparation and logical-verdict contracts.
Actual process creation, SMT bracket semantics, and solver IO remain adapters.

## Optional GHC fit ranking

The new rank module partitions fits by comesLast and takes the signed pool
prefix. A pool of at least two fits schedules one model action under timeout.
The intended pool is not an actual IO request receipt. A zero timeout can
return before the action starts. Lazy score sorting can occur after timeout.
Success sorts the zipped fit/score pairs. Failure and timeout return the
partition order. They do not restore the original interleaving.
Nonpositive pool sizes ask no question.

`SourceGhcFitRanking` reuses the installed source sortBy model.
It proves occurrence preservation for complete score vectors and no new
fits for every returned score vector. The exact unconditional result is a
permutation of the scored prefix. A short score vector drops the unscored
pool suffix through zip. DecisionModel requires one score per option.
The public constructor can violate that contract.

A fixed-response source probe confirms complete, short, empty, nonpositive,
and failure branches. It makes no external model request.
The probe is `/tmp/mcfta-ghc-ranking-source-probe-20261016.hs`.
Its output agrees with the checked prefix and partition behavior.
No production behavior was changed for this contract boundary.
Descending score order, stable ties, Double/NaN laws, request encoding, and
actual timeout and server IO remain separate proof targets.

## Validation

Strict Nix build passes all libraries, executables, tests, and benchmarks.
All six suites pass: 749 examples plus the golden suite.
Fourmolu passes eight changed Haskell files. Cabal-gild passes four packages.
The exact source and focused proof logs use `/tmp/mcfta-memo-workers-*`,
`/tmp/mcfta-conjunction-emptiness-*`, `/tmp/mcfta-declare-once-*`, and
`/tmp/mcfta-ghc-ranking-*`.
The full-library goal remains active.
