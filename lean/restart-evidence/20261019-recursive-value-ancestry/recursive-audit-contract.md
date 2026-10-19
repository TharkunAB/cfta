# Exact recursive values and selected reader entries

Read-only source review, 2026-10-19 11:26 CEST. No Lean job or production edit forms part of this review.

## Result

The exact-value ancestry proof has no material issue in the reviewed source.
Its source alternative retains the complete recursive value at the same natural child-index path.
Its event alternative retains an actual earlier leaf or Head event and a literal ordinary-child occurrence of the same value.
This is a useful result without a false gate on any changed class forest.
It is stronger than row-field ancestry.
It does not claim a complete selected-reader continuation through each later class.

The reviewed node snapshot is `64d2457c480ad16aa2d902522e40b61794a520770e9f97b3e5b014fdb13061d8`.
The reviewed fold source is `575bcd4e7094747ef30d139577598b8b40be466a5f1acf87caa4845940ccc125`.
The reviewed reader-entry snapshot is `09698d49e680af4ed1d4e591a59b5028c2b50971c554fe7a835039e555285d03`.
These are source-review hashes. This note does not certify pending build or printer jobs.

## Why the ancestry proof is substantive

`ClassRecursiveValueOrigins.Occurs` follows literal ordinary rows and children only.
It does not enter a stored Mu body or a union member.
It retains each selected row lookup as a receipt.
The path index contains child positions, so canonical row reordering does not change that path.

The node induction uses the actual constructor result to prove that an ordinary rebuild returns Empty or an ordinary node.
Such a rebuild cannot create a recursive root.
For a recursive descendant, the proof maps the selected canonical row to an actual raw rebuilt row.
The child induction then retains the same child position and the complete recursive value.
It does not infer child identity from symbol, guard, or arity alone.

For a Head branch, source ancestry inside the exposed value becomes `Event.head`.
That event retains the actual Head read and the actual recursive body edit.
An event inside that body becomes `Event.recursive`.
Neither case identifies the exposed value with the body return.

The class lift keeps the class's captured input forest and base heap.
The fold executes its tail before its head.
The proof derives the head-entry readiness, memo validity, availability, path domains, and native history from that actual completed tail.
The source case recurses through the tail with the same forest slot, child path, and complete recursive value.
The event case retains the actual earlier phase and each later head graph through `FoldEvent.tail`.

## Minimal next reader producer

The implemented `ProjectionRecursiveEntry` is the correct next bounded producer.
The reviewed source has no material issue.
It indexes an entry by the exact outer `Project`, final `Read`, selected position, and selected row.
Its ordinary case uses the existing `ProjectionFrame`, including the selected source row, projected operand interval, and exact nested call/read pair.

The first cut has two forms:

- An empty-path terminal read starts at a recursive value. Keep that exact read and row lookup.
- A nonempty-path projection first takes `Project.recursive`. Keep the recursive input, actual Head, actual body projection, and complete remaining read spine.

The ordinary lifts give `Occurs input prefix needle` for the exact recursive input at that cut.
The prefix must be a prefix of the requested path.
Keep that decomposition explicit, either in the entry indices or in a derived theorem.
No unrelated completed projection is needed.

The private `signed_lookup` proves `index = Int.ofNat index.toNat` from the actual successful signed selection.
A negative signed selection has no selected child in this implementation.
Thus the public producer can retain a general signed path without assuming its sign from `NodeClosed`.

`NodeClosed` is a visible selected-path assumption.
At an ordinary branch it requires closure only for selected children.
At an empty path or a recursive head it requires the relevant whole value to be closed.
This is not closure of every unrelated sibling.
It also excludes an open bare-reference terminal.
Do not describe this reader producer as unconditional for all open operands.

This typed entry plus current fold ancestry already gives a useful value-level source/event classification of the recursive input selected by the actual reader.
A separate edit-flow relation is not required for that limited conclusion.

## Source alternative after Required

The original false gate must remain tied to the original forest and its actual gate heap.
Use `RequiredRowOrigins.Origin` only for the initial original-to-prepared transition.
Do not infer this relation between later class forests.

The precise remaining source-only lemma is:

```text
actual false original NodeTrace for requested natural path
+ initial SemanticReady, UnionNormal, and Available
+ Origin original prepared
+ Occurs prepared prefix needle
+ Recursive needle
+ requested path = prefix ++ remaining path
    => Annotated Plain needle
```

The existing private `ClassObservationSpines.safe_gate` and `safe_origin` proofs supply the appropriate proof pattern.
At a recursive value, their safety relation can only use the plain-region case.
If a plain ancestor occurs earlier, its child annotations give the same local conclusion.
This lemma is a next proof obligation, not a theorem supplied by this review.

Excluding a selected nonplain observed row then still needs the actual remaining projection/read and its causal guard-heap and semantic support.
Do not manufacture a successful projection of the original forest.
Do not obtain finite-cap support or whole-value closure from exact ancestry alone.

## Event alternative and its exact limit

The same complete recursive value allows the consumer to keep its actual Head/read subcall unchanged at the selected reader entry.
The event witness also establishes a real earlier event containing that value through literal ordinary children.
These facts do not assert a completed projection of the whole event value along the residual path.
That projection would visit other rows as well.
Its success does not follow from one literal occurrence.

For an empty residual at an actual native result, an actual complete epsilon origin can feed `NativeOriginExposure.returned` or `request`.
Those endpoints retain the captured writer and retained-Mu unfolding.
For a nonempty residual, `NativeNodeRowLineage.ordinary` or `ordinary_body` can supply actual ordered child writers after the ordinary native branch and its selected row/child have been established.
A nonempty residual is not itself `Origin reader [event] row`.
A Head event also needs its retained body edit; it is not a native return by definition.

If a later theorem needs the particular output occurrence to follow one particular event through all later edits, add an indexed flow relation then.
Its output coordinate should contain the canonical row indices and child indices as data.
Its event coordinate should contain the residual row/child coordinates.
The ordinary constructor must retain the actual canonical-to-raw row selection, `Slice`, child call, and child-flow witness.
The Head source constructor must lift source flow through the actual body edit.
The recursive-event constructor must lift event flow through that same body edit.
The fold-tail constructor must retain source flow through the actual later head, rather than only its whole graph.
Each constructor should erase to the existing `Event` and `Occurs` facts.
Do not add a constructor from an arbitrary event and two independent occurrence facts.

The present `Occurs` path need not change for value-level ancestry.
If distinct row occurrences must be distinguished, an occurrence-specific flow should index the row coordinates as data; proof identity of an existential `Occurs` witness is not that coordinate.

## Inspected boundaries

- `ClassRecursiveValueOrigins.Occurs`, `node`: exact recursive value, same child path, no false gate.
- `ClassFoldRecursiveValueOrigins.children`, `list`, `class_sources`, `fold`: exact forest slot and chronological phase receipts.
- `ClassStructuralOrigins.Event`, `ChildEvent`, `RowEvent`: actual native/Head events and selected child slices.
- `ClassObservationSpines.ProjectionFrame`, `Spine`: exact outer projection/read indices and selected ordered intervals.
- `ProjectionReadSpine.Spine`, `project`: actual selected projection/read decomposition, including terminal Mu reads.
- `ProjectionRecursiveEntry.Entry`, `occurs`, `first`: exact first recursive reader entry or an ordinary full-row route.
- `SourceEqualityProjectionPathDomain.NodeClosed`: selected ordinary-path closure, whole recursive-head closure.
- `RequiredProjectionOrigins.project_read`: original false gate plus Required origin; no prepared false gate.
- `NativeOriginExposure.returned`, `request`: complete epsilon-origin consumer, not a literal-descendant consumer.
- `NativeNodeRowLineage.ordinary_body`, `ordinary`: actual ordinary native row and ordered child writers.

No source-syntax identity, source mass descent, global simulation, finite request bound, completion, or Haskell defect follows from this review.
