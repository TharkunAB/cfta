# Root integration review

Reviewed 2026-10-24. Target main c4f7319acf84213fccc8ea389487d4176e4f0b62.
Merge a7d667f628ee060501126efaf9d19bfe37ecfb72.

Root read the complete TH implementation, tests, package metadata, package
README, design note and ten-path integration diff before merging. The new
package generates a scalar observation view. It does not generate HasFTA,
a source codec, typing rules or invariant laws. Source constructor order and
arity survive the field-type erasure. Rejection and namespace checks remain
explicit. No concrete source defect was found and no Haskell fix was made.

The fresh focused suite compiled the new library and splice-containing test
under GHC 9.14.1, -Werror and one Cabal job inside nix-shell. Four examples
passed. Six successful splices and five recover checks are present. The
38-term typed test checks all ranks and roundtrips. The refined test checks
values and four unrank positions; its title does not establish refined ranks.
Formatting and package checks also passed. The four commands share a serial
4 GiB job with no swap and a five-minute wall-clock cap. The cap receipt and
fresh allowance sample are retained. No additional tests were required.

Existing Lean source and Audit imports are unchanged. The last strict checks
and 3675-job Audit remain evidence for the same source bytes. They are not
rerun here. No claim extends those proofs to TH or GHC Generic extraction.
SourceDeriveNodeViewNames, resolved typing and conditional codec laws can be
reused only after the emitted shape/build/read and original codec obligations.
Language equality alone does not give equality of numeric ranks.

Root reread the H6 public theorem. Its valid initial cache, recorded guard
allocation history, covered closed expression, formal guard interpretation,
empty inherited payload and sufficient mathematical width/fuel remain explicit.
It supplies actual finite node-call traces with exact finite-tree language
equivalence. It excludes withoutRedundantEdges and does not prove convergence.
The observer callback theorems do not supersede this combined statement.

The pre-merge baseline was clean. A backup ref retains its head. The archive
verifier checks every original file and permits exactly three upstream old-file
changes and nine status insertions. All Lean, old native implementation,
repairs, drafts, counterexamples and evidence survive unchanged. Seven upstream
paths are new. FINDINGS retains the external repair index first. All five
listed repairs remain incorporated. The goal remains active and incomplete.

The first archive attempt exposed an incorrect verifier assumption: merged
README was compared directly with main. It correctly keeps the existing four
lines that link the formalization. Root read both README diffs. The verifier
now checks the exact reviewed merge blob for each of the three old upstream
paths; it still recovers every original baseline blob. Upstream snapshots keep
main's exact bytes. The complete failed archive and its raw failure receipt
remain retained. No product source or proof repair was needed.
