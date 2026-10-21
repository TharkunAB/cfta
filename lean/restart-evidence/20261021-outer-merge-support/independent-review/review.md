# Independent mathematical review

Reviewed on 2026-10-21 at 02:42 CEST. The complete 904-line candidate is
`SourceCurrentOuterMergePositionSupport.lean`, SHA256
`8c5ba90e5495a71123fdc3689d27b4e1f6c19cf770efde15e08c4d0294390340`.
No material issue was found. This review owns zero Lean/Lake commands and zero
public proof pairs. It reuses the author's three complete public readbacks.

## Exact public result

`parent` (line 514) preserves `MergePositivePosition.Support` after an actual
successful allocated Parent call. It requires initial native-operation Good,
physical Merge Stored, and initial Support. On the live branch it also requires
the original field, inherited equality and children to be available. These live
premises are conditional on the raw contradiction test being false.

`reached` (line 865) preserves Support at the caller of an actual
`OuterExecutionAncestry.Reached` prefix. It requires initial outer Good, phase
Inputs and Support. `initial_reached` (line 894) derives the law from empty Merge
tables, native-operation Good, the actual probe heap and initial NodeReady. It
does not require a future outer return.

Support has the exact meaning in `SourceCurrentMergePositivePosition.lean:28`:
every selected full memo entry maps each positive result position to a positive
position in that entry's captured original. That original can already be a
prepared or edited value. It is not an initial-program source anchor.

## Proof and operational checks

The operand proof (lines 26-59) inverts the actual projection and Merge calls.
Projection supplies semantic readiness, costs and availability at the exact
intermediate heap. Physical Stored moves forward through the actual projection.
The actual Merge call uses the core allocated support law. The equality-instance
alignment uses Subsingleton equality and introduces no extra premise.

Native target leaves retain the Merge memo. Shared target-cache hits also retain
it. Cache misses follow the actual target computation. The edit proof follows
ordered child and row calls. Node and edge construction retain this table. The
class fold uses the actual tail-first worker schedule (lines 341-351), then the
actual current class. Scan and Required effects advance physical support but do
not change the Merge table. Parent follows the actual raw rejection, field load,
precheck, Required, class schedule and final construction (lines 514-557).

The outer mutual proof (lines 684-794) covers six successful call forms. Demand
and finish preserve the Merge component. Evaluating owners use readiness derived
from the actual captured owner, without replacing it by the queried request.
Mu reconstruction uses `MuReconstructionEffects.node_body`, whose completed
cleanup returns the same whole caller. Successful edge calls use the Parent law.
The subsequent row and child calls use the exact current Good/Inputs effects.

The prefix induction (lines 836-873) uses the actual
`OuterExecutionAncestry.Step`, not a larger synthetic relation. The physical
`OuterPrefixInvariants.reached` result supplies current Good and Inputs at each
step. It does not contain or assume the new Support conclusion.

## Unfinished-prefix boundary

The relevant Step definition is `SourceCurrentOuterExecutionAncestry.lean:326`.
Its `node_evaluate`, `body_rows`, `descendants_children`, `children_walk` and
`walk_head` constructors enter literal phases. Its `rows_edge` constructor
requires a completed earlier edge call. `rows_tail` requires completed edge and
descendants calls. `walk_tail` requires a completed earlier node call. Thus the
current node, body, row, descendants, children or walk phase can be unfinished.
The prefix does not enter an internal partial or failed Parent or Merge call.
The new theorem proves no law for that internal stopping heap. The module header
states this limit.

The private busy corollary uses an actual recovered prefix; it is not a fourth
public declaration. Neither it nor initial_reached assumes the future return of
the active node. The source has exactly three public theorem heads.

## Remaining limits

The theorem preserves the current table's per-entry support. It does not prove
positive-position support for an entire Parent/native output or restore an
initial forest source anchor. Old `MergePositiveRowOrigins.Writer/Raw` receipts
retain a historical call, but not Support of its writer-entry memo. No such
historical support is inferred here. The proof does not establish child-pair
retention, a native positive-position law, an original-binding rank, outer
completion, productivity, or Haskell refinement.

## Frozen readback

Selected author stems are `outer-support-direct-4` and `outer-support-public-1`.
The strict log is literally empty and the exact final source is retained. The
public log has 2,251,313 bytes. It contains complete check, full proof and axiom
readbacks for parent, reached and initial_reached, with all eight printer options,
no omissions and only propext, Classical.choice and Quot.sound. Both selected
receipts are terminal zero under effective 4 GiB max/high, zero swap and five
minutes, with fresh usage above one percent. Raw commands are preserved unchanged.

The owner selection records five commands: two failed elaboration attempts, one
successful unselected earlier draft, final strict and final full readback. This
review does not rerun those checks. ROOT-relative source pins retain the relevant
actual workers, prefix relation, physical invariants, core support law, historical
writer definition and toolchain. Snapshot verification is independent of the
original /tmp directory; --live also checks the chosen repository root.
