# Next completed-build binding ancestry step

Reviewed 2026-10-20. This is a source design note. No new theorem in this
note is claimed checked. No Lean job or repository edit was made for it.

## Existing contracts and the missing connection

`SourceCurrentBuildStructuralRowOrigins.build_row_origin` now derives an
actual node, captured slot or selected binder winner from a completed build.
Its capture branch keeps the exact lexical lookup. Its binder branch keeps
the exact final stored Mu and actual probes/request/finish. Neither branch
contains the original root of that value's source construction.

`InternedFreshOrdinaryActiveOrigins.Path` already retains actual source
callback crossings with arbitrary captured values. `Path.inputs` proves
that descendant inputs are a prefix of literal callback references followed
by the unchanged original inputs. `SourceHistory.Reached` adds growth from
those callback entries to the current source point.

`InternedFreshOrdinaryRootEncounter.build_encounter` and `complete_encounter`
derive rooted paths for pending active reservations. Their `RootScope`
tracks waiting keys and enclosing pending equations. These are genuine
producers, but their pending hypotheses do not cover completed resident Mu
writers. `SourceRecursiveIntersectionMaybeMuHistory` has the same pending
scope, including the prepared stored body's actual source root.

`SourceCurrentNativeMuIssuedHistory.build_path` derives issued publication
paths from actual builds. `IssuedWriters.from_empty` recovers a selected
writer with exact callback intervals. `Written.raw_contexts` exposes that
writer's actual raw source builds and warm replay. These contracts retain
the writer's own syntax and inputs. They do not link the syntax to an
original completed source call.

## Smallest substantive next producer

Implement a completed-build rooted writer theorem. A suitable general API is:

```lean
build_writer
  (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
  (before : State Symbol Guard) (context : Context before initial)
  (initialMuFree : forall key entry body depth ordinary,
    before.nodeRecords key != some (.mu entry body depth ordinary))
  (result : Value Symbol Guard) (after : State Symbol Guard)
  (actual : build root initial before = .done result after)
  (key entry body depth ordinary)
  (selected : after.nodeRecords key = some (.mu entry body depth ordinary)) :
  exists event : Publication,
    Reached root initial (.binder event.smart event.expression)
      event.environment event.before /\
    -- The SAME event supplies key/candidate equalities, first-write absence,
    -- issued prefix and all three callback paths, and final growth/issued
    -- suffix from the existing strong Written contract.
    StrongWrittenFields before after key (.mu entry body depth ordinary) event
```

`StrongWrittenFields` above is specification notation, not an existing head
or a proposed required abstraction. The implementation can return the exact
existing `Written` existential fields and the rooted receipt together.
Keeping them in one existential avoids an unproved alignment of two writers.
A closed-source corollary uses empty inputs and empty tables; it needs no
supplied ancestry predicate.

One implementation route is a private predicate on the actual issued Path.
At each publication subtree, record `Reached` for that exact event. Prove
this predicate while constructing the actual path by mutual source/list/edge
induction, using `Reached.node`, `union`, `enter` and `grows`. Adapt the
existing issued writer selection induction to preserve that same event's
rooted receipt. This derives the certificate from actual calls. It does not
assume that every publication already has the desired source ancestry.

An arbitrary issued Path alone is insufficient: it can sequence actual
publications from unrelated source calls. A path does not name an original
root or forbid additional executions after the root call. The completed
build equation and its source-directed derivation are therefore essential.

## Capture consequence and exact limits

For an existing rooted source path and an actual row-bearing captured slot,
`Path.inputs` can derive an indexed original-input suffix:

```lean
Path root initial expression inputs crossings ->
inputs[slot]? = some captured -> RowAt captured row ->
exists originalSlot,
  slot = crossings.length + originalSlot /\
  initial[originalSlot]? = some captured
```

A crossed local slot is a literal reference and has no structural row.
For empty initial inputs, that capture alternative is impossible. This
indexed suffix statement is useful only with a path that is actually
derived; it must not replace the missing completed-writer producer with an
assumed `Reached` premise.

The closed-construction consequence does not cover later reconstruction
captures. `InternedStoredSubstitution.execute` builds an encoded plan with
`leaves source |>.map (input environment)`. Its captures include whole closed
source values and external replacements. `StoredLeafShape.leaves_shape`,
`StoredSubstitutionScope.slot_lookup/build_closed/build_external`, and
`StoredSubstitutionBindings.global_lookup` already describe exact lookup
and binding behavior. They do not provide a completed writer's path back
to that particular encoded root. After that path is derived, an indexed
capture splits into a closed original leaf or a reference's actual optional
replacement. Arbitrary replacement maps require their own ancestry; their
availability does not imply an original binding.

For actual Mu unfolding the replacement map is concrete: only the exact
stored self name maps to the actual complete Mu. A future source-derived
capture theorem can retain that map and separate self replacement from
closed leaf capture. It must keep the actual stored value and lexical name.
It must not identify a warm selected writer with the current callback.

The proposed step gives honest original syntax membership and original
capture slots for one actual construction. It does not yet prove a global
renewal measure, termination, observed native operand ancestry, or Haskell
correspondence. Native memo History remains at the captured checked reader;
a rooted physical publication path does not transport native memo history
across an arbitrary later physical view.
