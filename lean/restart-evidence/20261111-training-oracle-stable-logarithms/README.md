# Stable current training oracles after PR207

Main a248ab6aa merges the numerical repair in PR207. The historical
20261111-training-oracle-overflow packet retains the failing old hashes
and output. This packet checks the current implementation.

The SAME singleton language a(a), bound 2, now runs at log-weight 400
and -400. It checks completion logPartition, both oracle log-partitions
and both normalized expectations. The correct partitions are 800 and
-800. The expected count of a is 2. Every result must be finite and
within 1e-9. Output is rounded only after those assertions pass.

Run check.py under the existing serial 4 GiB cap. It verifies exact
source hashes, formats the reproduction, builds the actual library
inside project Nix with GMP and runs it with GHC9.14.1. It creates no
binary archive. checked.json records those actual commands and results.
upstream-validation.json records the full generator suite, formatting
and two example checks at the same cap. repair-review.md records the
source review and remaining limits.

This is a runtime regression check for these finite inputs. It is not
a Lean proof of floating-point training or of every mixture fit. The
upstream suite also covers underflow and repeated equal-child weights.
No Liquid Haskell contract or dependency is introduced by this repair.
