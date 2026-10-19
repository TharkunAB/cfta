# Event path origins and separate native views

Updated: 2026-10-19 12:52 CEST. Start: `8282cca55`.
Source main: `184bba662`. Merge: `a3cf692cb`. Proof: `776875701`.

## System guarantee

Fresh construction always finishes in the Lean model. Under the stated
guard conditions, its result represents exactly the specified finite trees.
A completed supported root reduction with empty inherited constraints
preserves that language. General outer completion and Haskell refinement
remain open. Read `notes-current-system-claim.md`.

## Full row origins along a path

`SourceCurrentProjectionPathOrigins.PathOrigin` uses one physical view.
Its root case retains an epsilon Origin of the complete selected row.
Its child case retains an epsilon-origin parent row, an exact natural
child index and the remaining PathOrigin. It preserves full guards and
ordered children. Mu and union exposure belong to the epsilon origin;
they do not add a child index to the path.

`project_read` starts from actual Project and Read graphs and their
selected Spine. Initial semantics, costs and availability remain explicit.
The later reader needs semantic support, costs and forward Keeps from
projection return. The caller supplies a view that grows from the actual
read return. No whole-value closedness, guard heap or desired origin law
is a premise.

The Spine induction derives internal support through actual ordered
projection and read prefixes. Actual suffixes connect every internal read
to the final read return. Actual completed Head reads supply their full
row Origin at the common view. This does not transport an arbitrary
Origin through growth. It uses the completed read and its replay theorem.

`occurs` prepends a literal ordinary event occurrence to an observed
continuation. It retains the residual natural child path. It does not
follow stored Mu bodies, union members or observational unfolding rows.

## Actual class-fold composition

`SourceCurrentRecursiveEventPathOrigins.fold` consumes the previous
actual event-observation theorem. The original false gate, actual Required
preparation and actual FoldReads retain their existing support premises.
The result is an ordinary Route in the FINAL fold value, or an actual
earlier event contains the exact first recursive value.

The recursive alternative now retains a PathOrigin of the same full row
from that event. Its path is the event's literal residual followed by the
recursive value's actual remaining observation path. Its view is the
completed selected read heap. Actual projection and read effects derive
Keeps from the recursive projection entry to that heap. The captured
event Source remains at its earlier supported entry.

Preparation and fold share the returned forest, with separate supported
heaps. This result does not construct a complete chronological outer call.
PathOrigin is row ancestry. It does not construct a Project of the
unchanged whole event or assert that a deep row is an event root row.

## Native calls with a separate physical view

`SourceCurrentNativeOriginViewBranches.returned` retains a captured checked
reader with its actual native history and returned cell. Its selected row
Origin uses a separate valid physical view. Actual forwarding normalizes
the request to one chosen writer. No native memo state is assigned to the
physical view. The view need not grow from the query heap in this generic
contract; its Origin and validity are explicit.

`request` derives codecs, history, physical facts and the chosen returned
writer from an actual completed request. The Origin still uses the
separate view. The conditional Mu result keeps that writer's actual body
execution at the captured reader and an actual stored unfolding at the
physical view. It does not identify these two executions.

`ordinary` first derives that the actual ordinary compiler returned an
ordinary value. Its epsilon Origin therefore selects a literal physical
row. The theorem recovers both indexed input rows, the full conjunction,
the exact paired child request and Good child endpoints. Both original
operand children have strictly smaller mass than their respective query
inputs. No source-row positivity premise is needed. The generated output
child need not have smaller mass.

The ordinary conclusion retains child-heap growth into the captured query
reader. It does not export native Retained from that child return or its
returned-cell writer. Repeated normalization of the child still needs
that memo provenance. A later proof must recover it from the actual
ordered row and child schedules. No child-entry History is assumed.
The existing row producer retains the actual edge-call return in the
captured reader. Its warm edge-writer receipt then keeps only heap growth.
The next foundation must retain the native memo relation from that same
earlier edge-body return to the chosen checked reader, as the existing
node-writer receipt does.

`union` recovers the exact original member index, actual ordered prefix,
child call and suffix. The selected member has smaller source mass. Its
child return is retained in the captured reader and has Forwarded there.
The same complete row has Origin at the physical view of that child result.
No mass bound is placed on the generated child result.

`reference` retains the actual entered name, captured read, operand order
and resolved child call. Forwarded belongs to the captured checked reader.
The full row Origin remains at the physical view. Reference resolution
has no strict mass claim.

A PathOrigin child supplies its exact parent epsilon Origin, selected
child and remaining path to these native handoffs. A nonplain deep row
does not prove that the earlier parent or Head row is nonplain.

## Constructed checks

The path check builds an event wrapper around the existing two-row source.
An actual projection selects outer row index 1 and internal Mu-read index
0. The actual calls derive PathOrigin from the source at [0]. A literal
event occurrence at [0] gives the combined event path [0,0]. The selected
deep row has no root Origin from the event. The theorem proves both facts.
It assumes no whole-event Project.

The native-view check builds a closed native query and derives its actual
Trace, Good states and history. A new physical edge increases the heap's
edge count. An actual row Read then supplies Origin at this distinct
later heap. The native request handoff keeps its writer at the captured
query return. The result is ordinary; the check does not exercise its
conditional Mu unfolding conclusion. It assumes no native history at
the physical view.

Neither check instantiates the full original-false-gate outer composition.
Neither asserts finite productivity, a language failure or a Haskell defect.

## Validation and remaining work

The full default build passes 3459 jobs. Audit checks 73817 axiom dependencies.
All nine public declarations and two constructed theorems pass complete
proof printing and standard-axiom checks. The three production and two
constructed strict logs are empty. The sole full-build warning remains
the unused `inputs` binding in InternedFreshOrdinaryClosedCompletion:24:5.
Lean jobs use Lean 4.34.1, a 4 GiB cap and zero swap. Failed elaborations,
blocked wrappers and the rejected initial fixture packaging remain in
`restart-evidence/20261019-recursive-event-source-read/`.

Source-origin renewal, active-owner exclusion including empty owners,
general outer completion, repeated-pass convergence and Haskell refinement
remain open. The actual ordinary child memo handoff is the next concrete
producer. The full-library objective remains active.

Main changes six earlier Haskell files and adds OrderedFrontier. The other
261 earlier Haskell files retain their bytes. The ordered cursor, prepared
template exclusion and mandatory-pair subsumption worklist need additional
implementation proofs. Read `notes-current-upstream-ordered-enumeration.md`.
No Haskell build or test result is claimed. No local Haskell behavior
patch or repair request is added. FINDINGS retains all external repairs.
All earlier proofs, counterexamples, repairs, drafts, stashes and worktrees
remain preserved. Publication awaits direct approval. No push or board
write is attempted.
