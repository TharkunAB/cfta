# Independent indexed projection and Merge row review

I read both complete final production sources and the projection fixture.
I found no material logical issue. This review adds no Lean declarations or
Lean executions. The earlier guard component remains unchanged.

## Indexed projection

`rows_indexed` distinguishes source positions from output positions. A
missing selected child produces no recursive call and no output. That case
increments only the source index. A selected child produces one output.
That case increments both indices. The prefix uses `take sourceIndex` and
`take position`. The suffix drops the selected source and output with the
corresponding index plus one. The retained middle call projects the actual
selected child. It does not project the source row as a value.

`union_row` starts with membership in the actual returned `nodeEdges`.
`makeNode_edges` identifies that list with the canonical surviving rows.
`normalized_member` then gives membership of the same complete row in the
pre-normalization read result and proves `dead row = false`. The private
`read_all_member` identifies an indexed operand, its actual row read, and
its exact earlier and later read schedules. The output row is therefore an
actual canonical survivor supplied by that read. A read can unfold Mu. The
proof does not assert that the row was already a physical row of the
operand before the read. It does not identify an initial source occurrence.
The explicit SemanticReady, operand availability and closedness assumptions
supply the read effects and physical coherence. No future row law occurs.

The fixture builds a closed ordinary source with three rows. One row has
no selected child. The actual row worker returns two values without changing
that constructor heap. The public statement fixes output position one and
uses `rows_indexed` to obtain its source index and intervals. It also uses
`union_row` on a later canonical output row. The source index remains
existential in the public statement. It does not claim the literal numeral
two. The fixture does not test a recursive Mu operand.

The first fixture full-print attempt exits zero but contains `failed to
pretty print expression`. It remains unselected. The second full-print
attempt terminates with exit -15. Its metadata does not establish the cause.
The selected fixture uses a private checked witness and a public alias with
the same complete statement. Strict six has a zero-byte log. Public three
passes the full printer and axiom checks. I compared the alias change with
the earlier source. It retains the same construction, proposition and proof.

## Merge positive rows

`Writer` retains an actual historical completed body run with its entry
semantic, cost, stored-memo and input availability facts. `Raw` requires
such a writer for each completed entry and preserves its complete original
physical key. `call` preserves Raw through actual instructions. It rereads
the actual stored winner and uses `hit_original` to identify the full input
from physical residency and reference injectivity. It does not identify a
new candidate with an older winner without this argument. Initial Raw is
an explicit historical assumption. No arbitrary table is claimed to have
it automatically.

`positive` means that the complete returned guard differs from the supplied
Top guard. It does not mean that its stored own field is nonempty. In a
closed ordinary input, the proof follows the actual group schedule. A group
with more than four rows constructs Top and cannot supply the selected
non-Top output. A small group retains the original symbol and complete
guard while it requests every child in source order. Final makeNode
readback first removes dead rows and duplicate identities. The selected
surviving complete row is then traced to an indexed row of `nodeEdges input`.
Its children retain an actual ordered recursive Merge run. The conclusion
does not equate the returned child values with the original child values.

Open ordinary inputs and all other constructors follow the unchanged body
branch. The theorem keeps that identity alternative explicitly. It does
not require all public inputs to be closed. The underlying Merge graph is
a completed sequential projection. It does not model pending ancestors or
runtime publication order. The new origins do not prove outer termination,
a decreasing source rank, or a bound on renewed own-field occurrences.

## Literal target operand adapter

I also read `SourceCurrentActualMergeOperandOrigins` in full. Its private
`stages` proof inverts the actual operand bind into the exact projection and
Merge calls. Projection leaves the result memo unchanged. The proof derives
the actual Forest graph, intermediate semantic and cost facts, and projected
value availability from the literal projection. It transports Stored through
the derived projection Keeps. Raw retains historical facts without a heap
parameter, so no backward heap transport is required.

`operand` converts the actual nonempty physical own payload into complete
guard inequality with Top. It applies the Merge call writer producer and
positive row origin theorem. Its index refers to `nodeEdges projected`.
That projected value can result from union or recursive exposure. The proof
does not identify an original forest row or derive a strict source rank.
Initial semantic, cost, physical stored-memo, lexical values and Raw facts
remain explicit. It does not claim arbitrary physical stored tables contain
actual historical writers.

## Final reviewed receipts

The selected groups are projection-indexed-public-1 (two public pairs),
merge-public-1 (four public pairs), memo-public-1 (one public pair), and
projection-kernels-public-3 (one constructed pair). I ran the existing
hardened checker read-only on all four groups. Each passes all eight printer
settings, complete proof printing, the standard three-axiom restriction,
no-omission checks, and effective 4 GiB memory / zero swap receipts.
No review Lean process was launched. The production strict snapshots and
fixture strict-six snapshot exactly match the final reviewed sources and
have zero-byte logs. The three canonical builds completed. They replay only
the pre-existing ClosedCompletion unused-input warning.

The review owns zero public and zero constructed declarations. It reuses
seven public and one constructed pair. It excludes the owner's mutable
memo and Merge fixture work, all root peaks, all global selections and all
authority documents. The frozen 30-pin guard component remains unchanged.

## Source pins

| Path | SHA256 |
| --- | --- |
| `lean/MicroCFTA/SourceCurrentProjectionIndexedOrigins.lean` | `143b94d6471f9baebd754012e3e5b4d029ac74a52d1bfd77323c3fe3b41f352a` |
| `lean/MicroCFTA/SourceCurrentMergePositiveRowOrigins.lean` | `da628f5ba46e01d3213b53de49250e8396ed07d28e80dd0a97ee24183451685e` |
| `lean/MicroCFTA/SourceEqualityProjectionGraph.lean` | `b39e09930df5bd935cded34a7aa3ad17ba467be6d434b071cdd844060a709ccb` |
| `lean/MicroCFTA/SourceEqualityProjectionUnion.lean` | `4c9634175c628fff77305282f43d71a0108c44a54965606417d81597a7401833` |
| `lean/MicroCFTA/SourceEqualityProjectionRead.lean` | `f299b66171bdf9452fa2b62b22ddca3371a1fb4916193a57d1fd5ece59f8551d` |
| `lean/MicroCFTA/EqualityLeafProjectionPhysical.lean` | `95c18033cc3fb94339a4198af7950c3f904c656a98870ffcf13736ef80201467` |
| `lean/MicroCFTA/SourceCurrentMemoMergeGraph.lean` | `5701546cc13508e40e8cfc07cf48330cc6b353f6d880211aa1d8520562a0092c` |
| `lean/MicroCFTA/SourceCurrentMemoMergeEffects.lean` | `59e412eb3b6fe5089af77b4d2f3f79fae69bedefd2eab29e874853a907f77d5b` |
| `lean/MicroCFTA/SourceCurrentActualMergeOperandOrigins.lean` | `030159f0b8fe674275b67cb096f2e3689de86e095316932fdb4b3f9cc4348eef` |
| `lean/MicroCFTA/SourceCurrentAllocatedTargetWorkerSound.lean` | `428adb9b25b6bba78921b2bed7e156d09a009c36164b30b133e953145b6eb167` |
| `lean/MicroCFTA/SourceEqualityProjectionCosts.lean` | `56b09c5ba2da1aabe7249b1e51cda3df7891ae9cc42d5585b17b54c70bf25bc4` |
| `lean/restart-evidence/20261018-selected-renewal/projection-kernels.lean` | `bf2501d2c8858e129886a9b5c349c7eb4f9d6580e91c742e1c988025a5fdcd4c` |
