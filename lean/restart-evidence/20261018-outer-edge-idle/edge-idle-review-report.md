# Independent edge-idle review and next node obligation

The review found no material proof issue. The three new modules derive
edge idle at actual reached phase entries, recover the exact source of an
edge-memo diagnostic, and exclude every edge-memo diagnostic from the stated
initial semantic and edge-idle facts. The review also checked the existing
`SourceCurrentOuterEdgeIdle` dependency. None of these results proves general
outer completion or excludes a node-owner collision.

## Final source and receipt pins

| Module | SHA-256 | Strict / canonical / public |
| --- | --- | --- |
| `SourceCurrentOuterEdgeIdleReached` | `b5e0b3e1eaa7e3942f0781c84b11748d979c2180bc32991d7dc6d179b64d2b06` | `edge-idle-direct-1` / `edge-idle-canonical-1` / `edge-idle-public-1` |
| `SourceCurrentOuterEdgeMemoFailure` | `8066eec5ed6361cb00437bd8f1ef4a938cb526a176ef1a65096c537056288bbb` | `edge-dispatch-direct-2` / `edge-dispatch-canonical-1` / `edge-dispatch-public-1` |
| `SourceCurrentOuterInitialEdgeMemoFailure` | `5105ef6915a9088287a4e51ef7f48194473cac78e28ee380d022aef5b0e93bb1` | `root-edge-global-direct-2` / `root-edge-global-canonical-2` / `root-edge-global-public-2` |

The reviewed existing `SourceCurrentOuterEdgeIdle` dependency has SHA-256
`4ced480a88de5e01db05579b1019635626d5c7207d626b3d1cadc31357032ba5`.
The three selected strict logs have zero bytes. All selected canonical
runs complete. The selected public groups pass the hardened checks for
two, one and two full pairs, respectively. They contain all eight explicit
options and use only permitted standard axioms. The receipts record
4 GiB maximum/high memory limits and zero swap. Only the existing
`InternedFreshOrdinaryClosedCompletion` warning remains in canonical logs.

## Exact retention scope

The existing `EdgeIdle` predicate excludes evaluating cells only in the edge
family. It permits arbitrary node-family activity. Its `Safe` predicate is
asymmetric: a successful outcome has an idle edge table; a failed outcome
does not report an edge-busy diagnostic. It does not assert edge idle at a
failed endpoint. In particular, a failed Parent body can retain its edge
owner in the evaluating state.

The actual edge body makes no outer recursive request. A successful demand
finishes the selected edge handle before descendants start. The private
ready and finish proofs retain the exact table cells at every other handle.
They do not assume that arbitrary supplied tables are well formed.

`OuterEdgeIdleReached.step` covers every constructor of the literal
`ExecutionAncestry.Step`. The row-head transition uses the successful edge
call. The row-tail transition uses that call followed by the successful
descendant call. The walk-tail transition uses the successful earlier node
call. Other steps leave the edge table unchanged. `reached` iterates these
facts. This relation does not contain the failed Parent's internal entry or
terminal failure state. The result needs no semantic or capacity premise and
no successful enclosing-call premise.

## Exact diagnostic and global exclusion

`OuterEdgeMemoFailure.failed` inverts the literal failed execution for all
six outer phases. It returns the exact reached `.rows (fuel + 1)` entry and
its exact failing edge call. The result retains the original row suffix,
the actual caller, the diagnostic handle and payload, and the final caller.
Earlier completed equations come from the observed failure. The theorem
does not assume a future successful traversal or a semantic read graph.

`OuterInitialEdgeMemoFailure.edge_no_memo_failure` separates two facts.
Edge idle excludes busy. Valid lookup links exclude an absent cell. Ready
returns cannot fail. The evaluate branch preserves the captured owner and
cannot emit an edge-memo diagnostic: its edge body can emit only a Parent
diagnostic. This local theorem does not exclude Parent faults.

The global `no_edge_memo_failure` theorem applies `InitialPrefix.reached`
to the derived row entry. Its returned Context supplies current memo
validity. `EdgeIdleReached.reached` supplies edge idle at the same caller.
Both facts concern the literal failing edge call. No candidate-owner
replacement or future resource entry is used. The initial Context, Frame,
Fits, guard carrier, Inputs and scheduled Room remain explicit semantic
support. Physical Good alone does not replace them. No lower-fuel ceiling
is needed to exclude this diagnostic: the proof uses actual completed
earlier summaries rather than assuming their completion.

The first root strict attempt exited zero with three warnings. The review
detected the nonempty log. That attempt and its canonical receipt are
unselected. The final source changes only section-variable scope and a
redundant simplification. The selected strict log must contain zero bytes.

## Next node-owner producer

The next key obligation concerns every actual `walk_head` request, not only
its immediate caller. `ExecutionAncestry.Ancestor` records each enclosing
activation and the exact unfinished body-to-current prefix. For a dispatched
request `q`, the missing exclusion is `owner.key != q.key` for every still
evaluating ancestor owner. The key contains both inherited identity and
resident Value identity. `OuterInitialBusy.busy` already identifies the
complete colliding request when a busy result occurs. Context and physical
growth do not make that collision impossible.

`PositionalOriginChain.mass_lt` decreases from an explicit pre-edit anchor
to a preserved positive-row continuation. `OuterPositionalDispatch.edge_dispatch`
also derives the actual subsequent call, but that call dispatches the
reconstructed value first. It does not identify successive runtime entries
with consecutive steps of the conditional chain. Required unselected
footprints are local to the actual row. They do not pass from an enclosing
row to a nested row. `OuterOriginalRepeat.original_reappears_with_new_inherited`
also shows that the same original Value can recur while its earlier owner
is active. The inherited key changes and the example completes. Thus strict
Value identity or original-row identity is not a valid general rank.

The most direct missing output producer is visible in
`NativeQueryRowOrigins.RowOrigin` and `returned`. Self and ordinary terminal
branches already supply exact source rows or joined rows with ordered native
child traces. The `bothMu`, `leftMu`, `rightMu`, union and reference branches
still return an explicit `Residual`. Refine these branches with the actual
captured writer's reconstruction or exposure rows and ordered child calls.
Use the actual chronological Mu publication and retained winner. Do not
replace that writer by the current callback candidate.

`NativeMuPublication.History` supplies actual publication chronology.
`StoredReconstruction.mu` constructs the selected payload's body and
ordinary reconstruction schedules, but asserts no equality between them.
`RetainedMuWriterAlignment` closes the selected earlier writer comparison
only under that writer's static BinderFree condition. The general used
branch must not inherit that restriction as an unstated global premise.
For branches ruled out by the closed-input facts, prove the exclusion
instead of assuming a reconstruction source.

Then compose those produced origins with `ClassFoldRowOrigins.fold/pass`
and the actual Parent-to-walk dispatch. The target is an exact source-anchor
handoff for the runtime request, including selected edits and recursive
exposure. This is an output construction task, not a supplied rank premise.
It must precede any claim that the conditional positional chain covers all
outer branches. General used-binder reconstruction and the all-ancestor
measure remain open where the existing residual classification stops.

Even complete active-key exclusion needs a separate finite fresh-call bound
or well-founded measure to prove unbounded completion. A finite own-guard
carrier does not by itself bound inherited constraints. The existing
`OuterInheritedGain.collision` and `OuterRowFieldOrigins.gain_source` derive
an intervening nonempty own-field gain with an exact earlier full row.
They do not exclude that gain. `InheritedGainDomain` bounds one combination
from its own operands, not every future recursive operand. No new infinite
execution or Haskell defect is established here.

## Evidence boundary

The manifest selects three new production modules and five existing full
public pairs. It also pins the reviewed old edge-idle dependency and the
source portions used for the next-proof recommendation. The independent
review adds no Lean declaration, build, or constructed example. The root
owns its constructed fixture; this manifest excludes that mutable fixture
and its receipts. All selected strict, canonical, public and effective-limit
checks are recorded by `edge-idle-review-verify.py`.
