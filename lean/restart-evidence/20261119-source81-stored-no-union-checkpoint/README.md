# Stored substitution preserves heaps without union records

Code d02df8ee9a5cd397a95c2cd1b7965aeeea970c58 adds one normal Lean module and
its Audit import and13 queries. Read FINAL-HANDOFF.md for the exact assumptions,
checked results, failure history, current strongest claim, and next proof gap.

Run `python3 verify.py --current-tree` from this directory to check this archive
and the6303 current source/toolchain inputs. Omit --current-tree to verify the
historical archive after later source edits. This command does not rerun Lean.
Private58493 and normal89762 contain the compiler checks. Their complete logs,
controllers, inputs and actual terminal receipts are in inputs.tar.xz.

The source contains4public and9private authored theorems plus4Prop predicates.
The9private lemmas are the same9helpers. True module ownership includes37
compiler-generated theorems. Metadata adds no proof credit. This component does
not establish one model for all historical constraints or original-root acceptance.

List the archive with `tar -tJf inputs.tar.xz`. Extract it in a separate checkout
or an empty directory; member paths are repository-relative. parent-links.json
binds the earlier Source80 and causal-progress archives. They are not copied.
Their source snapshots supply the older inputs referenced by this checkpoint.
The standard Nix/Lake build can reproduce the normal source proofs from the
code commit. The archive includes the exact capped five-gate commands and
source maps for a replay in the original workspace layout.

The archive contains source, scripts, commands, logs, metadata, input maps,
and preserved failures. It contains no executable binaries, compiler objects,
cache copies or private namespace mirrors. The XZ payload compresses repeated
text snapshots together to keep the checkpoint small. No /tmp cleanup is needed.
