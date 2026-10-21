# Independent Merge positive-position review

Reviewed 2026-10-21 02:26 CEST. No material issue found.

Candidate: SourceCurrentMergePositivePosition.lean, 626 lines, SHA256
59ebe7865a3ca865b6cb65a17c1d51db35e935ad6fa6ddb9b87d86e34c4e2282.
I read the complete statement and proof. I also read the listed operational,
normalization, row-field and table foundations. This is an independent source
review. I did not author this module or its new private helpers. I ran no Lean
or Lake command for this review.

The six public declarations are Support, support_empty, run, call, worker,
and allocated. Support is the complete captured-original table invariant.
It is stronger than physical Stored. PositiveAt uses child indices. It does
not use canonical row indices as path components. It keeps unions transparent
and Mu values opaque. A positive row means that the full plain test is false.

## Actual proof and recursion

Lines 45–60 define private positional postconditions. RowPositions retains the
selected child index. Lines 263–287 keep All₂ across actual ordered maps.
The request certificate assumes the smaller request law only as a local
Certified contract. Lines 529–587 then discharge that contract by the actual
mutual Run/Call induction. On a miss, body_certified is applied to that same
body Run. The proof does not assume the whole output's desired support law.
The public call theorem supplies only the literal request certificate.

Small groups retain each source row's guard. Their actual ordered child calls
produce All₂. The output child lookup selects the source child at the same
natural index (lines 347–374). Large groups process the actual columns.
columns_indexed (81–103) derives row[index]?=some value at the same index,
including empty earlier rows. The large proof uses this indexed receipt at
415–418. Its unordered columns_member fact is used only for physical input
availability and closedness. The new Top root cannot create positivity because
topPlain is an explicit premise (376–410).

Actual makeNode normalization can remove or reorder rows. Lines 107–126 recover
a source row by canonical survivor membership. The same row keeps its child
list. No source/output row-index equality is claimed. ordinaryUnion derives
its source edges from the actual input lists. makeUnion covers empty, singleton,
all-ordinary and stored-union branches (189–258). In the stored-union branch,
coherence and resident full records recover the actual complete member list
from its key. This covers warm constructor hits. It does not equate references
with full values without the required physical facts.

Selection supplies a literal retained subset through select_exact. It does not
supply a desired positional output premise. The comparison parameter clear is
arbitrary because selection only removes alternatives. Closedness and the
actual physical contexts remain explicit where those facts are needed.

## Warm results and state scope

Support refers to entry.original, not a guessed current argument (27–43).
On a hit, hit_original derives equality of that complete captured original and
the actual input from physical Stored, current availability and semantic
readiness. On a miss, recursive calls may have installed an earlier winner.
The proof retains the current table's Support, adds the actual candidate law,
then rereads winner_found and aligns its original (576–587). It does not return
the candidate law as if the candidate necessarily won.

worker uses the actual fuelled completion through call_sound. allocated uses
the actual allocated worker's complete done equation and its sound graph.
Call.graph erases only the separate equality-allocation operation. The result
and memo remain exact. Its positional and physical conclusions concern the
exact before.heap and after.heap (613–624). It does not claim that the two
complete allocated states or their equality-allocation fields are equal.

Mu, union, reference, Empty and open ordinary body branches return their exact
input. The traversal processes closed ordinary roots. The theorem does not
unfold a Mu body or infer positives behind an opaque barrier.

## Scope and selected evidence

The theorem needs supplied Support for arbitrary warm initial tables. Empty
Support follows from support_empty. This package does not prove transport of
that invariant through Parent/Outer prefixes, native support, termination,
a global rank, language equality, or Haskell refinement. No finite Plain cap
is required for this Merge law. Actual completion is a premise, not a result.

I independently read the selected strict3 receipt and its empty log, and the
selected public1 full readback. The latter prints all six full statements and
proofs with all eight requested options. The 172695-byte log has no omissions
or printer diagnostics. Every reported axiom is in the standard set. Both jobs
have recorded 4 GiB max/high, zero swap, five-minute limits and fresh usage.
These are reused owner receipts. This review owns zero jobs and zero proof
pairs. The separate verifier checks exact snapshots and live ROOT foundations.
