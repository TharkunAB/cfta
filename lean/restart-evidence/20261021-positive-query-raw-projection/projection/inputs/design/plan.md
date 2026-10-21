# Positive observations through a raw corridor

Status: source audit and implementation plan only. No new Lean theorem is proved. This package runs zero Lean or Lake commands. It changes no official source, prior evidence, or frozen review. The proposed scope is two public observers and a small private corridor induction.

## Result

Use the existing actual indexed read spine. At a full corridor, call the existing public capped observer. At an ordinary corridor step, follow that spine's same selected source row and child. Recurse on the remaining corridor. Do not copy the capped observer's collect, read, Head, or recursive exposure proofs.

A finite projected result does not provide a cap for its captured input. An ordinary input can have an unrelated child Mu that is not hereditary Plain. RawCorridor.node requires the corridor only in the selected child column of each raw row. A full input cap would also constrain that unrelated Mu. SourceCurrentRawCorridorProjectionCap.project proves the output cap, not this stronger input premise. No checked counterexample or new source family is claimed here.

## Exact proposed public scope

Use the same fixed native Symbol and Guard types as CappedProjectionPositivePosition. Keep its actual call, selected full row, and reader premises. Replace its capDepth and bounded arguments by:

    corridor : RawCorridor (path.map Int.ofNat) value

The root observer takes the following existing objects and hypotheses:

    path : List Nat
    project : Project (path.map Int.ofNat) value before result after
    read : Read result reader rows readAfter
    position : Nat
    row : Row
    selected : rows[position]? = some row
    semantic : SemanticReady before
    costs : CostHeap before
    available : Available before value
    guards : GuardHeap Plain before
    readerSemantic : SemanticReady reader
    later : Keeps after reader
    readerGuards : GuardHeap Plain reader
    corridor : RawCorridor (path.map Int.ofNat) value
    nonplain : SourceMemoGate.plain row.entry.key.constraint = false

Its conclusion is PositiveAt value path.

The child observer retains that same project, read, position, selected row, semantic and reader support, and corridor. It replaces nonplain by:

    childIndex : Nat
    child : Node
    chosen : row.children[childIndex]? = some child
    positive : PositiveAt child residual

Its conclusion is PositiveAt value (path ++ childIndex :: residual).

These are unchecked signature sketches. No public caller supplies a Spine, desired origin, returned input cap, output positivity law, original false gate, closure proof, UnionNormal, native History, or future completion. There is no additional reader CostHeap premise. Natural paths match the existing positive-position relation. This plan does not assert the same conclusion for arbitrary negative signed indices.

## Reuse and private proof work

1. Call SourceCurrentProjectionReadSpine.project once for the supplied actual project/read/selected row. It already retains the source row index, projected operand index, canonical output row index, raw union row index, operand read index, source child selection, actual ordered projection prefix/suffix, and actual ReadAll prefix/suffix. Do not identify these indices.
2. Use a private three-line RowPositive definition with the same two cases as the capped observer: a nonplain root row, or an exact ordered row child with PositiveAt at a residual path. This joins the two public cases without adding a public abstraction.
3. Induct on the natural path while generalizing the actual spine and input. At RawCorridor.full, unpack its explicit cap and dispatch on the residual: call CappedProjectionPositivePosition.root or .child on the same supplied project/read/row. This reuses every actual Mu/union read exclusion already proved in that module.
4. At RawCorridor.node, the path is nonempty and the input is an ordinary node. Spine.root is incompatible with the nonempty path. Spine.recursive is incompatible with Recursive of a node, which is False. The remaining Spine.ordinary case provides the same actual source row and selected child. Apply the corridor's all-raw-row child hypothesis to that exact sourceSelected and childSelected. Recurse on the exact call and operandRead in the spine.
5. Use public projection/read effects to derive semantic heaps, costs, availability and Keeps at that child's call and operand read. Lift the returned PositiveAt child proof with PositiveAt.child at sourceIndex and the same natural child index. Canonical reordering never changes the selected ordered child position.

Only a small guard restriction helper is needed in addition to RowPositive and the corridor induction:

    Grows earlier later -> GuardHeap Plain later -> GuardHeap Plain earlier

This follows directly by applying the later Heap certificate to growth.nodeRecords key fullMu present. The current Heap definition is conditional on each exact full record; Grows retains that same record. This is backward restriction of an existing record property, not a claim that growth creates a causal History or transports arbitrary native memo invariants.

The new module can be about 130 to 180 lines with two public heads and explicit dependent indices. This is an estimate, not a checked size. No old module needs an edit or an export of a generated private name.

## Actual intermediate guard and read cuts

In Spine.ordinary, use these exact fields:

    projects : ProjectRows path index sourceEdges before values projectedMiddle
    reads : ReadAll values projectedMiddle allRows unionMiddle
    built : run (makeNode allRows) unionMiddle = (result, after)
    projectPrefix : ProjectRows path index (sourceEdges.take sourceIndex)
        before (values.take operandIndex) start
    call : Project path child start operand finish
    projectSuffix : ProjectRows path index (sourceEdges.drop (sourceIndex+1))
        finish (values.drop (operandIndex+1)) projectedMiddle
    readPrefix : ReadAll (values.take operandIndex)
        projectedMiddle earlierRows readStart
    operandRead : Read operand readStart selectedRows readFinish

Derive resident source rows from the initial semantic heap and available node. Apply rows_effects to projects and projectPrefix. The cached source row, edge_grows, and childSelected derive Available start child. Apply project_effects to call and rows_effects to projectSuffix. The latter receives source-row residency grown through the actual prefix and child call. Apply readAll_effects to readPrefix with projected-middle support. These are the same open effects used by the old capped spine proof; none requires a cap on unrelated siblings.

For guards, first derive Guards after using public ProjectionGuard.node on the SAME whole ordinary project. Apply union_effects to the SAME Union.node reads built and the derived projected-middle facts. Its growth restricts Guards after to Guards projectedMiddle. Then restrict that certificate along call-growth followed by projectSuffix-growth to obtain Guards start. Apply public ProjectionGuard.readAll to the SAME readPrefix to obtain Guards readStart. This avoids copying the old private rows_guards induction.

For the recursive observer's later-read premise, compose projectSuffix Keeps finish->projectedMiddle with readPrefix Keeps projectedMiddle->readStart. This yields the exact Keeps finish readStart used for the SAME operandRead. Its semantic support and guards are derived at readStart. Do not replace readStart by the final external reader or assume a new history at that cut.

The public root and child wrappers provide the original external reader's semantic/guard/later facts. Full-corridor branches use them directly in the public capped observer. Ordinary branches use the earlier actual operand read retained by the spine. Both branches keep the selected full row and its child data.

## Alternatives inspected

- CappedProjectionPositivePosition.root/child, lines245-261, are the exact full-corridor fallback. Its private read_positive, collect_positive, head_positive and spine_positive are not reusable public names. They need not be copied.
- ProjectionReadSpine.project, lines193-199, already supplies all ordered ReadAll and ProjectRows provenance. Its private read_all_member need not be copied or made public.
- ProjectionCosts rows_effects, readAll_effects, project_effects and union_effects supply the needed open effects and exact Keeps intervals.
- ProjectionGuard.node and readAll are public. Its joint ProjectRows guard endpoint is private. Backward restriction along the actual suffix avoids adding or copying that endpoint.
- TargetOperandPositivePosition.project, lines511-546, needs a literal original false gate, a Required Origin and initial UnionNormal. Those are not implied by a raw corridor at changed phase values. Its private Accepted/project_origins route is a larger duplicate and is unnecessary for this scope.
- RequiredProjectionOrigins.project_read, lines436-457, is the installed public Required-based row origin counterpart. It also needs the original gate and Origin, and handles a nonplain selected row rather than a plain row with a positive descendant. Exact searches found no installed file or namespace named RequiredOpenReadOrigins. The new proof does not depend on that shorthand.
- ProjectionPathOrigins.project_read retains epsilon Origin at a later view, including Mu exposure. That relation alone cannot imply PositiveAt of an opaque Mu input. It also needs reader CostHeap and a retained readAfter view. It is valid provenance but does not shorten this proof.
- RecursivePlainRead.project/project_read preserve hereditary annotations forward. They are useful existing Plain laws but do not invert a finite raw corridor through unrelated nonplain siblings.

## Placement in the chronology result

ClassCorridorChronology.fold/pass/indexed_phase returns the actual changed phase forest, Current and Merge stores, and an ordered All2 relation that preserves every original raw corridor. all2_signed transfers an entry mask to the same signed forest slot at that phase. The new observer can consume that phase value's transferred corridor and its actual projection/read. It returns PositiveAt of THAT phase value at the full natural path.

The chronology relation preserves corridors forward. It does not transport PositiveAt backward to the original entry value. The latter still requires genuine native/Merge positive support and any necessary same-cell source rebase. This plan does not close that separate ancestry step. It also does not establish child separation, active-owner exclusion, renewal, arbitrary unfinished-call invariants, outer completion, or Haskell refinement.

## Validation and next action

This package contains a source audit, exact snapshots and a portable hash/range verifier only. It contains no proof candidate, constructed fixture, public proof pair, Lean run, runtime run, or successful elaboration claim. The next implementation should add only the two root/child observers and the private ordinary corridor proof. Obtain explicit implementation authorization before starting proof jobs. All previous frozen packages remain unchanged.
