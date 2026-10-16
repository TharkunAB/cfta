# Independent review of initial outer resource construction

Reviewed on 2026-10-17 at 00:09 CEST. Result: PASS. No material defect was found.

The review covers the final `OuterResourceDefs`, `OuterResourceEdge`,
`OuterResourceChildren`, `OuterResourceRows`, `OuterResourceNode`, and
`OuterResourceRoot` modules. It includes the final `prepared_root` endpoint.
The manifest records exact production bytes and separate frozen copies.
The review changed no production source.

## Initial premises and construction

`OuterResourceDefs.lean:35–55` defines headroom from the current constructor
counters and two initial request allowances. `Headroom.after` consumes an
actual `ConstructorWorkTrace` through `ActualOuterWork.WorkBounds`. The trace
bounds the next counters at the exact returned heap. It does not assume
suffix capacity at a future state.

`OuterResourceDefs.lean:70–80` defines `Below` as an internal smaller-rank
induction interface. The public list helpers take this interface explicitly.
`OuterResourceNode.lean:173–182` discharges it by strong induction on node rank.
The public node and root constructors do not take a completion callback,
future result law, completed enclosing graph, or range Plan.

`OuterResourceEdge.lean:56–69` derives each captured owner's parent capacity
at the literal begin-evaluate state. The initial soundness and coherent heap
give equality of the complete owner value and candidate value. The begin
operation keeps the checked state. Thus the original profiles and headroom
apply to that exact owner. `ParentUniformCapacity.complete` derives the
reached parent checks from those initial facts. The call is then constructed
at lines 70–72. Its quantitative certificate is produced from the same reads
at lines 73–75. No desired parent certificate is a construction premise.

## Source order and suffix supply

`OuterResourceChildren.lean:84–111` splits the initial child-list allowance
into one head and the original suffix. It constructs the literal indexed
descent, then the smaller node call. `ActualOuterWork.node_call` consumes the
same head reads. `Headroom.after` gives suffix headroom at that head's exact
returned heap. Original suffix values remain available through the actual
effects. Active-frame preservation restores the ancestor bound. The code
does not use the head's result as an input profile for the original suffix.
The contradiction branch at lines 141–145 erases slots without child calls.

`OuterResourceRows.lean:132–180` charges each source row in this order:
parent call, returned-parent descendants, original row suffix. The first
actual Work trace leaves descendant and suffix supplies. The returned
parent's universal certificate supplies its changed row, arity, and guard
envelopes at lines 150–165. Its `EdgeNarrow` height bound proves that each
returned child has smaller node rank. The descendant Work trace then leaves
the original row suffix supply. No profile of a future child result is
assumed.

The descendant constructor at `OuterResourceRows.lean:63–95` derives the
actual inherited prefix before walking children. The prefix changes no
constructor heap. The budget retains one raw edge request after the walk.
`OuterResourceNode.lean:69–91` similarly retains one raw node request after
the original rows. These charges agree with `OuterBudgetNumbers.lean:22–49`.
They count literal occurrences, including repeated keys. Warm hits can use
less Work; they do not require a distinct-key assumption.

## Owner, state, and semantic alignment

`OuterResourceNode.lean:107–150` treats ready and evaluate observations
separately. A ready observation retains the complete state. On evaluation,
the proof transfers the complete stored owner value, its domain, the initial
profiles, and its rank before constructing the body. `node_finish` uses the
actual body law and exact published handle. The quantitative producer then
consumes those same reads. It does not supply a premise used to construct
that body.

The result bundles retain strict reads, reached Checks, full `Post`, actual
availability or residency, all earlier causal stores, and positional
narrowing. The final worker `StableRun` follows from the constructed graph.
No independently chosen execution replaces that graph. Global memos and
inventory use the same computed endpoints as `Post`.

`OuterResourceRoot.lean:77–87` combines that constructed node return with
same-read quantitative and Work producers. It retains the complete earlier
receipt and obtains final zero-reservation headroom from actual Work.

`constructed_root` at lines 90–133 assumes a valid initial equality cache,
covered allocation history, finite ordinary source syntax, and initial
constructor supply. Its capacity quantifier at lines 98–99 ranges only over
the result of source allocation. It does not range over a completed
reduction. The theorem constructs that allocation and reduction itself.
It derives the empty inherited payload, strong cold stores, initial active
bound, exact full-language equivalence, actual Work, and final headroom.

`prepared_root` at lines 136–171 also derives the covered field history from
the literal preparation result. It preserves the same initial headroom
condition. The preparation premise concerns original field readback. It is
not a future reduction or result-certificate premise.

## Current source comparison and limits

The encoded schedule agrees with `cfta/src/Data/CFTA/Equality/Operations.hs`:
the empty inherited entry at lines 68–81; parent before returned-child
descent at lines 87–96; contradiction before indexed child calls at lines
143–145; and local RequireAll followed by the tail-first class pass at
lines 206–242. The raw graph preserves those indices in
`SourceCurrentAllocatedPartialGraph.lean:46–117`.

This is finite construction for the current allocated ordinary model under
explicit initial supply. It includes Empty and finite ordinary nodes with
arbitrary admitted guards. It does not establish general recursive-node
termination, fixpoint termination, concrete CAF publication, or GHC demand
correspondence. The older universal raw-Reach numeric Plan bridge remains
separate. This construction does not claim to prove that bridge. The full
library objective remains open.

## Validation

The final root canonical build passed with 1667 jobs in
`resource-root-prepared-canonical-2.log`. The earlier root-chain build passed
with 1667 jobs in `resource-root-canonical-1.log`. These logs replay only the
historical unused `inputs` warning in
`InternedFreshOrdinaryClosedCompletion.lean:24`.

`root-resource-independent-public.lean` independently checks all 16 public
declarations in the six modules. It prints each full explicit signature and
axiom report from canonical imports. The strict pinned Lean invocation
returned exit 0 in `root-resource-independent-public-1.log`. The log contains
16 axiom reports and no error, warning, or `sorryAx`. This review added no
production theorem or new integration claim.
