# Joint source laws and generic native composition checkpoint

The published starting checkpoint is 0ebb832d. The backup branch is
backup/formalize-before-joint-native-producer-20261017-0435.
Source main is c0cc8a05. Its local merge is 896b0a1c.
The initial formalize pull completed without a source change.

## Proof commits

- ad5c409b: guard heap retention, probe support, and actual binder returns.
- bd85cd40: shared joint context and literal heap effects.
- 86d2c5f1: actual branch, row, Mu, reference, and full source-fuel induction.
- 1a0ad30e: exact generic native transfer and conditional cold completion.

## Validation

The final pinned full Audit passes 2816 jobs and 62897 axiom dependency
checks. Only propext, Classical.choice, and Quot.sound are allowed. All
11 current production sources pass strict checks without diagnostics.
The final imported checks pass 83 axiom/full-signature pairs in 17 groups.
Eight component manifests verify 198 entries. Read expected-validation.json,
checkpoint-validation.json, and checkpoint-verification.log for exact data.

The first full Audit passed before unused-instance cleanup. The final Audit
rebuilds Calls, Execution, and NativeJointClosed after that cleanup. Final
root and independent imported signatures use those rebuilt dependencies.
Calls direct attempts 2 and 3 were warning-only. Attempt 4 rejected the omit
syntax and warned about that command. Attempt 5 restricts the instance to
the one theorem that needs it and passes with no diagnostic. Execution's
final strict replay also passes. All raw attempts and sources remain.
Canonical replay retains only an older unused-input warning.

Preservation retains 11398 starting files, all 2804 older non-Audit production
proof sources, all 239 Haskell files, and the complete active package trees.
The Audit adds only the eleven imports. Seven restart authorities receive
current status updates. There are no other baseline changes. All 68 frozen
production manifests verify 573 entries. Stashes and three other worktrees
retain their initial state. Earlier external drafts that were already
unavailable have no recovery claim.

## Scope

The full bounded source executor derives the joint returned laws from actual
initial context and operands. No future successful child or desired output
law is assumed. Native exact meaning transfers the result to its identical
machine. The generic cold endpoint constructs its finite execution, with
WordRanges explicit. The actual warm-return endpoint verifies a supplied
return. Neither endpoint proves the current checked equality-cache Control
lift or general initial numerical ranges. Concrete cold/warm integration
derives ranges only for its own literal paths.

The full source gate and whole-library goal remain open. Continue from
next-native-ranges-and-checked-control.md. Do not repeat the joint source
induction or weaken the final source contract to hereditary leaf support.
Preserve the optimized interned core, earlier constructor and equality work,
all proofs, counterexamples, repairs, and marked drafts.

No Haskell behavior change or new Haskell defect occurs. Root FINDINGS keeps
the external repair registry first. The recursive field-pool repair b9219b9e
is merged and locally validated. Reuse the unchanged strict Nix build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence.
