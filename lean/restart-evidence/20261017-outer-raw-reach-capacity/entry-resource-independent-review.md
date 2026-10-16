# Independent review of raw Reach resource admission

Reviewed on 2026-10-17 at 00:22 CEST. Result: PASS. No material defect was found.

The review covers the final `OuterResourceEntryDefs`,
`OuterResourceEntrySteps`, `OuterResourceEntryReach`, and
`OuterResourceEntryRoot` modules. The manifest records exact reviewed bytes
and separate frozen source copies. No production source was changed.

## Current entry invariant

`OuterResourceEntryDefs.lean:42–114` defines admission for all eight original
entry controls. Each case contains current Context, causal stores, inherited
equality readiness, resident finite ordinary inputs, numeric shape and guard
profiles, input height, and current constructor headroom. Node calls and
bodies use the appropriate active-rank bound. List controls retain a common
ancestor cap and bounds on their literal remaining inputs. A parent body
needs no outer recursive active condition because its lower parent
calculation does not call the outer worker.

Admission contains no completed graph, strict read, future output
certificate, or Plan. The parent-capacity projection at lines 120–128 uses
the same current Context and uniform initial supplies. It derives capacity
before that parent executes.

## The original Step relation

`OuterResourceEntrySteps.lean:35–251` covers all TEN constructors of the
unchanged `OuterEntries.Step`. It adds no restriction to that relation.
Node and edge evaluation transfer the complete captured owner value from
the actual begin observation. Publication keeps the checked heap and all
earlier stores. Node publication also establishes the pushed active bound.

The three transitions with completed earlier prefixes are the important
cases:

- `rows_descendants`, lines 104–134, accepts the original bare earlier
  EdgeCall. `OuterPrefixResources.edge_call` independently constructs a
  valid prefix and identifies its complete return by raw worker uniqueness.
  Its strict receipt and actual Work therefore apply to the supplied earlier
  graph. The returned parent's certificate supplies the changed profile.
  Narrowing proves that its returned child ranks remain below the ancestor
  cap. The actual Work leaves descendant headroom at the exact return.
- `rows_tail`, lines 135–180, first performs the same edge alignment. It then
  aligns the supplied earlier Descendants graph through the closed
  descendant constructor. The two actual Work bounds leave the original row
  suffix supply. Effects retain the original suffix residency. Active-frame
  preservation restores its ancestor cap.
- `walk_tail`, lines 222–251, constructs the literal indexed descent before
  aligning the supplied earlier NodeCall. That call's actual Work leaves the
  original child suffix supply. Its complete returned caller, computed
  inventory, global memos, and stores supply the tail admission.

These cases assume only earlier raw completion, as the original Step
constructors require. They do not assume an enclosing or next completion.
`OuterPrefixResources` breaks the potential proof cycle through the already
closed initial-headroom construction. It does not call the new Reach Plan
or a root theorem that depends on that Plan.

The remaining transitions use original input projections, literal
inherited-prefix or descent effects, and initial profile bounds.
`descendants_children` retains the returned raw edge field and changes no
constructor heap during inherited combination. `walk_node` uses the exact
descended inherited payload. Active ranks depend on the input value, so
changing that payload does not invalidate the child bound.

## Full Reach and root composition

`OuterResourceEntryReach.lean:22–29` proves admission on the original
reflexive-transitive Reach relation. It does not replace Reach with an
annotated or semantically restricted relation. `numeric_plan` at lines
32–37 projects current parent capacity at every reached edgeBody.
`ranges` at lines 40–50 derives the older reached-machine-range Plan from
those same admitted entries.

`OuterResourceEntryRoot.lean:70–75` derives this numeric Plan from initial
admission before invoking the preserved conditional quantitative root.
The public result returns the Plan as a conclusion. It is no longer an
input at these new root endpoints. Lines 76–81 retain the exact earlier
strict reads, full Post, universal certificate, actual Work bound, and final
headroom at the same result and complete caller.

The source constructors at lines 84–169 retain the original field-history
and allocation semantics. Their only capacity quantifier ranges over the
original source allocation result. It does not assume that reduction
completes. `prepared_root` derives that field history from actual
preparation, then uses the same initial supply. Exact full-language
equivalence still follows from the allocated empty inherited payload.

Thus this new chain discharges the older universal raw-Reach numeric Plan
under the stated initial ordinary-input resources. The earlier checkpoint's
note that this bridge was separate remains accurate for its frozen source;
the present additive modules provide the bridge.

## Validation and limits

The final canonical root batch passed with 1685 jobs in
`entry-root-canonical-4.log`. Earlier failed aggregate attempts remain in
the evidence directory. They are not treated as final successful builds.

`entry-resource-independent-public.lean` independently imports the final
root and prints all ten public axiom reports and full explicit signatures.
The strict pinned Lean command returned exit 0 in
`entry-resource-independent-public-1.log`. That final log has no error,
warning, or `sorryAx`.

The result concerns finite ordinary allocated inputs, including Empty and
repeated positions, with explicit initial constructor supply and legitimate
warm invariants. It does not prove general Mu/reference termination,
fixpoint termination, concrete CAF publication, or GHC demand transfer.
The full library goal remains open. This review added no production theorem
or new integration claim.
