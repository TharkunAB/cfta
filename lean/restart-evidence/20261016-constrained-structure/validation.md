# Finite ordinary native structural validation

## Verified result

Eight additive source modules have canonical builds with exit code zero.
The full Audit completed with 2500 jobs and 59028 theorem dependency checks.
The only permitted axioms are propext, Classical.choice, and Quot.sound.
The old unused-input dependency warning remains. No new source warning occurs.
Read audit-build-1.log and validation-results.json.

Final imported probes check 68 public declaration axiom/signature pairs and
28 integration kernel pairs. They include arbitrary guards and nonempty
equality classes, metadata readback, both operand bounds, checked accepted
and rejected branches, arity mismatch, exact finish owners, literal cold
publication, an exact-state warm repeat, and a second finite native call
at the first actual returned state. Final probe logs have no errors,
warnings, or sorryAx. Earlier failed drafts remain in this directory.

The Code and Execution public probes belong to the root. Component reports
record the other final source hashes, public declarations, and kernels.
execution-review.md records a separate source review. It found no circular
parent result premise. next-class-progress-review.md records the next target.

## Preservation

verify-preservation.py --require-current passes. It reads the starting
5837-file snapshot and retains every file. All 2491 older non-Audit proof
sources retain their bytes. The only Audit change adds the new top import.
Thirty-three frozen manifests check 257 module entries. All 234 starting
Haskell files, all 206 active-package files, historical repair text, stashes,
and three other worktrees remain unchanged. No previous evidence script
was rerun or overwritten.

The proof commits are 106e4123, 5d54241d, a4506576, and 62f30089.
Source main remains c0cc8a05, merged at 896b0a1c. Remote readback confirms
that source base. No Haskell patch is added. Reuse the unchanged source's
strict Nix all-component build with -Werror, tests and benchmarks;
798 examples plus golden; six-file Fourmolu; and four-package Cabal-gild
and metadata checks. Their logs remain in
lean/restart-evidence/20261016-drawn-fields-local-worker/.
FINDINGS.md retains the current b9219b9e field-pool repair handoff first.

## Limits

Finite.finite constructs its actual finite receipt. Initial Good,
SemanticReady, Stored, Idle, available domain operands, and reached
WordRanges remain inputs. Domain and both operand height bounds apply
to the same returned state. Original syntax and closedness are derived.
The seen-pair list is empty. Arbitrary warm tables still need structural
admission; cold tables derive it.

The result does not prove general constrained outer reduction progress,
Mu constraint migration, unequal-length equality semantics, repeated-pass
convergence, current frontend adapters, concrete runtime correspondence,
or full-pipeline composition. The full objective remains active.
