# Fixed-reader row alignment and union clauses

Checked on 2026-10-18 at 22:11 CEST. Proof checkpoint is `aed9deb8`.
Starting checkpoint is `4af95a7b`. Source main remains `c0cc8a05`.
The local branch is `formalize`. The full-library goal remains active.

The target remains whole-library correctness against the intended semantics.
This checkpoint removes a fixed-reader source-fragment obstacle. It does
not prove full source simulation or whole-library correctness. The broad
reduction guarantee and exact size-query assumptions are unchanged.
Read `notes-current-system-claim.md` for those claims.

## Checked production results

| Module | Public heads | Result |
| --- | ---: | --- |
| `SourceCurrentGeneratedRowSchedules` | 1 | Actual node-source rows retain a common historical row index, complete symbol and guard equality, and ordered mutual Generated child outputs. It consumes actual row calls at one reader. |
| `SourceCurrentCausalRowFragmentAlignment` | 1 | Causal history derives equal output child Empty tests and exact row-survival parity for those row fragments. |
| `SourceCurrentFixedReaderUnionClauses` | 2 | A public historical SourceCall contract and actual union clause assembly keep the original reader. Strict-member atom and row obligations remain explicit. |

## Actual row calls

The row schedule consumes both historical node source calls, their Contexts,
Aliases, recursive lexical Inputs, replacement availability, forward growth,
and available raw results at one Ready reader. A selected original raw row
has one actual RowCalls there. Every opposite physical raw row has an actual
RowCalls there. The theorem does not assume either whole raw-node stored
execution or a desired output comparison.

The actual source edge calls identify a common source row index. Complete
historical prefix, child, edge and suffix receipts remain in the result.
Original raw-row survival supplies live child support. This permits child
Aliases without availability of unused lexical inputs at the reader.
Actual ordered stored child calls supply both Generated directions. The
result retains the full guard, symbol and child order.

The causal alignment theorem adds History from empty tables to that reader.
Causal Generated Empty agreement then gives pointwise child Empty equality.
The actual children.any Empty tests are equal. The two reconstructed row
survival tests are equivalent. No child semantic comparison or supplied
Empty equality is used. Actual whole-subgroup results remain unnecessary.

## Union assembly at the same reader

The assembly theorem retains two actual historical union calls and their
raw availability and growth. Both parent filters and stored calls are warm
at the original reader. Exact raw buildMany replays identify the original
ordered member values. These are source replays, not whole member filters
or stored executions.

Each fragment obligation receives the original source expression index,
both raw members at that index, and both historical SourceCall receipts.
An atom obligation also receives its exact retained literal atom and actual
stored return. It must produce an actual retained opposite atom call in
the corresponding original member, with literal clauses from the first endpoint to the second endpoint.
The assembly derives literal inclusion of that opposite endpoint in the
opposite parent result. It transports the clauses through this genuine
inclusion. It introduces no additional source relation step.

A row obligation receives an original literal row, its actual RowCalls and
its true survival test. It must supply an opposite literal row, actual
RowCalls, opposite survival and a full row match. Exact opposite coverage
places that reconstructed row in the opposite parent result.

The conclusion is one directional literal Clauses statement at the original
reader. It is conditional on those fragment obligations. It does not prove
Law for all unions, both directions, a global Directed instance, or full
language equality. The at-most-one-source-pair normalization relation stays
exact. No arbitrary transitive source closure or backward observation
transport is used.

## Actual integrations

The row integration constructs a closed binder over the body
union[[Depth,leaf0,leaf1],leaf2]. Its warm parent supplies the first actual
row call and every needed opposite row call. Its actual construction
supplies Ready and History. It invokes the new alignment theorem while
both the enclosing subgroup filter and its Depth-to-Empty reconstruction
increase the node counter. This checks the actual call interface.

The union integration constructs a raw union with a retained Depth atom
and a nullary row with symbol 3 and guard false. It uses the unrelated own
name uninterned 99. Its actual filters and stored calls are warm. The empty
source relation and reflexive actual fragment endpoints instantiate the
union theorem. This checks both atom and full-row assembly routes. It does
not assert semantic acceptance of the false guard.

Both fixtures use nullary rows. They do not exercise a changing recursive
child semantic comparison. The general row theorem permits arbitrary
ordered children and nested Mu source children under its stated premises.

## Remaining proof

Next define and prove the source-fragment law described in the independent
fragment contract review. Actual parent atom-call and row-call families
must restrict through root unions. The outer parent's bare-self selector
must remain explicit. A member's standalone-self exception cannot replace
that selector. Full subgroup filters and executions must not be assumed
warm to apply a strict member induction hypothesis.

The node-source row case is available. A literal row inside an arbitrary
member need not be a physical row of that member. Nested unions and
smart-unused binders therefore need their own source cases. Existing binder
readback retains an epsilon Origin; it does not directly give literal raw
row membership.

Reference slots need genuine semantic lexical induction. Selected used-Mu
writer generators give actual membership and schedules, but not their
literal successor clauses. A current source child or selected writer body
is not a smaller Generated recursor premise. A new body membership that
contains the parent proof cannot be passed back to the parent's induction
hypothesis. Current requester syntax can differ from the older writer.
Mu epsilon unfolding also preserves observation depth. These facts require
a justified progress argument or a stronger semantic publication invariant.

The pinned progress review identifies a smaller membership producer first.
It generalizes actual publication reconstruction to two distinct available
local replacements with mutual Generated membership. Both actual warm
body and ordinary call equations must stay explicit. That producer would
not prove semantic clauses or the original-reader cold-Mu continuation.
Read `restart-evidence/20261018-fixed-reader-row-clauses/progress-review-next-step.md`.

General completion still needs active-owner exclusion, fresh-call bounds
and repeated-pass convergence. Haskell correspondence still needs demand
and cache behavior, machine integers and external interfaces. No Haskell
bytes change. No Haskell defect or repair request is added. FINDINGS retains
the external repair registry first. The field-pool repair remains fixed.

## Evidence

Evidence is in `restart-evidence/20261018-fixed-reader-row-clauses/`.
All three production modules have actual zero-byte selected strict logs,
clean canonical builds and complete public proof/standard-axiom probes.
Four public and two constructed heads are checked with all eight printer
and linter options. Full Audit passes 3408 jobs and 73092 dependency checks.
Only the existing ClosedCompletion unused-input warning remains.
All Lean jobs use the pinned Lean 4.34.1 toolchain under a four GiB max/high
memory cap, zero swap and a five-minute limit.
