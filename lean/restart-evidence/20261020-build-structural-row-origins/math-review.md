# Mathematical review of completed-build structural row origins

Reviewed on 2026-10-20. The reviewer also wrote the isolated prototype.
This is a separate full-source mathematical review. It is not an independent
author review or another Lean verification run. The candidate is unchanged.

Candidate SHA256:
`e2d956d21a707f5ec052f1c929286ca8742353d884b90fabfe7e8a07831c89b6`.

No material logical issue was found in all 315 source lines or the directly
used normalization, row-call and selected-request interfaces.

## Exact rows and indices

The producer keeps the same complete `EdgeValue` row, including children.
It does not weaken that row to equal symbols, guards or arity.

The node branch first obtains the actual canonical output lookup from the
supplied `RowAt`. Actual `makeNode` readback gives membership in the surviving
original row list. The source index then selects that same complete row.
`row_call` follows the actual ordered source execution. `RowCall.source` and
`RowCall.selected` use the same source index for `EdgeSyntax` and raw output.
Its `called`, `made`, `earlier` and `suffix` keep the actual child build and
allocation interval. Its output equality connects those receipts to the
canonical selected row. Historical contexts and growth follow actual effects.

The canonical output index and original source index are separate roles.
They can be equal. No inequality or index equality is asserted. If equal
rows occur more than once, the source index is one genuine indexed preimage.
The theorem does not select a unique occurrence or preserve proof identity.

The union branch uses actual normalization facts from the actual intermediate
context and actual member availability. Its inversion separates literal rows
from whole opaque Mu atoms. It does not unfold Mu. The selected original
member index is shared by the source expression and returned value lists.
`member_call` retains the exact source prefix, selected call and suffix.
The recursive conclusion uses that exact call, same value and same full row.
Flattening and deduplication can give several valid original occurrences.
No claim identifies a unique original union occurrence with the input proof.

The capture branch follows the exact variable lookup. A missing slot returns
Empty and cannot supply `RowAt`. No capture source syntax or binding history
is assumed or inferred.

## Selected binder and smart cleanup

`NativeBinderExecution.decompose` inverts the actual current binder execution.
It derives the actual callback schedule and later context from the supplied
initial context. `NativeRequestProbes.request_probes` uses the actual request,
final facts and available complete probes. Its winner inversion covers hits
and the actual keep-first result after a miss. The candidate stores that exact
final cell and `finish` equation together. It never identifies the selected
stored body with the current callback body.

`finish_row` covers every smart branch. A raw binder exposes its stored body
through structural `RowAt.mu`. Smart-unused cleanup returns that exact body.
Smart-used cleanup retains the Mu and gives the same body projection.
Bare-self cleanup returns Empty, which has no structural row. No desired
body comparison or future execution premise enters these cases.

The selected stored payload is exact at the actual return heap. The relation
does not include the payload's publication writer, writer syntax or causal
history. Such a receipt needs actual issued history; `Context` alone does
not provide it. The implementation does not claim that stronger conclusion.

## Non-circularity and limits

The producer assumes only the initial semantic `Context`, literal completed
build equation, and actual structural row. The only recursive use of the
producer is on a strict original union member with its derived context and
actual call. There is no supplied future `SourceRow`, semantic origin,
parent-output comparison or reader history premise.

Node child calls execute the original ordered child syntax, but the theorem
does not recursively classify their descendants. Capture and binder-winner
alternatives are deliberate stopping points. This is a source-call
classification, not original binding ancestry, an observational Mu origin,
a global renewal bound, termination, or Haskell correspondence.

No Lean jobs were run for this review. The existing selected strict receipt
is `prototype-direct-4` with zero log bytes. The existing full public group
is `prototype-public-1`, two full heads, all eight printer options and only
standard axioms. Counts: zero owned proof pairs or runs; two reused public
pairs; zero constructed pairs; no canonical-build claim.
