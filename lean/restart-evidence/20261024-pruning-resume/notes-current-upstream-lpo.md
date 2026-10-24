# Main LPO repairs integrated

Updated: 2026-10-24. Main: `0db62d26b87e8e55b6c2719f6312ece6f93ed31b`.
Merge: `504523e47a9b85c5dc5f24a396dbf12baf54f290`.
Base: `74104221af2bdc2d0ccf454658170dd9a253545a`.
Backup: `codex/backup-lpo-main-20261024-0248`.

PR #169 changes only Specftacular.Rewriting and its README. Every other
baseline file and the new untracked matcher were preserved at the merge.
The 127096-file baseline check found 127094 unchanged files and the two exact
upstream replacements. Earlier proofs, drafts, counterexamples, repairs and
the optimized interned core remain. No local Haskell patch is added.

## Repair behavior

Commit 70a252537 uses erased program equality in the LPO subterm and equal-prefix
comparisons. The retained typed annotation-cycle witness now gives [GT, LT, LT],
both before and after canonicalTypes. A focused public-API probe checked every
comparison pair and every transitivity triple on those three terms and their
canonicalized forms. This finite check does not prove the general order laws.

Commit f484c0ca0 retains the uncurried path order. Its recorded function-context
reversal remains: f a > a and (f a) x < a x. The repair changes its consumers.
rewriteStep carries the actual application context through function positions.
It tests the instantiated rewrite in that context. addEquation requires an
additional appliedGreater check before one-way orientation. Both the principal
and specialized pruning-template branches require the same check.

The public addLawRules/reducible/pruningTemplates probe uses the retained valid
f a = a equation. The local f a is reducible. The enclosing (f a) x is not
reducible by that increasing change. The reverse a x is reducible to its
smaller application. No pruning template is produced for the unsafe direction.
The check therefore tests the changed rewrite and pruning behavior, rather
than require the underlying comparator reversal to disappear.

Commit 3ea886098 corrects the README schedule count. It lists eight separately
seeded cases, 40 boundary/list cases and 16 predicate/list cases: 64 extras.
The implementation schedule is unchanged. Finite testing does not prove laws.

## Verification and remaining obligations

The Specftacular goldens passed inside nix-shell with strict GHC warnings.
They include the existing LPO and KBO cases in checked and unchecked modes.
These cases use phase 1 and do not establish phase-4 pruning correctness.
Fourmolu passed for the changed Haskell path. Cabal-gild passed for the active
Specftacular Cabal file. No Cabal source changed. The unrelated CFTA suite was
not rerun for this two-file repair.

Both native probes compiled with -Wall -Werror and passed. The first probe
harness attempt did not expose cfta. The second exposed two text packages and
failed on ambiguity. The successful attempt hid unrelated packages and used
the exact package IDs from the current Cabal plan. All attempts and raw logs
remain in the evidence. These harness failures are not product failures.

General transitivity and well-foundedness on the intended typed term domain,
substitution stability, argument-context compatibility and the appliedGreater
criterion remain formal proof obligations. The criterion must also justify
longer spines and its synthetic variable names. No new native defect is claimed.
Template production, compiled pruning and partial-match pruning soundness need
separate proofs. The matching and observer theorems concern supplied templates.
They do not prove the safety of this producer.

FINDINGS marks both recorded LPO repairs as merged in PR #169. External work
needs no additional patch for the retained witnesses. Keep those witnesses and
the general proof obligations. H6 remains strongest combined. The full goal is
active and incomplete. Read notes-current-pruning-resume.md for the next target.
