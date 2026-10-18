# Conditional fixed positive continuation chains

Reviewed on 2026-10-18. The production module has five public declarations.

## Exact theorem

Below c next anchor has a literal selected row witness in some result.
The result can differ arbitrarily from the anchor. Link c anchor result
must hold. The selected row must have nonempty effective own equalities,
and its child c must be exactly next. No original-source carrier is given.

mass_lt applies PositionalOriginDescent.continuation. wellFounded embeds
Below c in the strict natural order on InternedValueMass.value.
The finite budget is mass(anchors count) + count <= mass(anchors 0).
It assumes the exact consecutive Below witnesses only below count.
Every value has positive mass, so count is strictly below initial mass.
no_infinite applies that budget at count equal to initial mass and derives
a contradiction. It does not assume an upper bound on reconstructed values.

The fixed child index is shared by every step. Every next Link anchor is
the preceding retained child. Replacing that anchor by the preceding
reconstructed result, an earlier contributing guard row, or a memo owner
is not permitted by these statements.

## Actual worker scheduling boundary

AllocatedPartialWorker.rows first completes edgeCall, then calls descendants
on the returned edge. descendants computes the inherited prefix and walks
that returned edge's children. walk dispatches nodeCall on each returned
child, in order. nodeBody on an ordinary value starts that value's row pass.

A Parent relation at forest slot f has source A = oldChildren[f] and
reconstructed result B = returnedChildren[f]. The worker first dispatches
B. If row R of B is positive and its child c is X, Link c A B gives
Below c X A. It does not give Below c B A.

The next Parent for R receives X at slot c. Its returned slot c is another
reconstructed value C. That worker dispatches C. A positive row of C can
give the next chain step only if the next Link source is the exact X.
Thus an actual spine must retain the source slot, row occurrence, Parent
return, and dispatch offset across two levels. It cannot identify the
forest slot f with the nested row-child slot c without this proof.

The worker also traverses other rows and other child positions. The theorem
bounds a supplied fixed positive chain, not every scheduled request.
A plain row does not satisfy Below. An inherited-progress argument must
handle such a phase separately before a combined termination argument can
use this chain. Conditional well-foundedness is not active-key exclusion.

Source: SourceCurrentAllocatedPartialWorker.lean:75-96,110-173.

## Existing repeat boundary

OuterOriginalRepeat uses G = [[[0,0],[0,1],[1]]], C = G[T,T], and A = G[C,C].
Its actual Parent returns [A,C] while the earlier A owner is still active.
The repeat changes inherited key, and the following precheck erases its
children. It is not a busy recurrence or an infinite trace.

That changed child-0 step does not satisfy Below from its earlier C anchor:
A has larger structural mass. A hypothetical Below witness would contradict
mass_lt. Equal complete guards and arities cannot supply that witness.
The example's paths differ from the later fixed untouched-child footprint.
It does not refute that footprint or this conditional chain theorem.

Source: OuterOriginalRepeat.lean:42-68,116-126,140-151 and its public theorem.

## Constructed integration

The one public fixture has no premises. It copies the private initial
construction from the frozen lineage-descent fixture. It builds positive
ordinary source nodes with recursive children. Actual guard allocation
supplies Ready and Good. Actual Required preparation and two class edits
supply Link through prepared_pass. The selected positive row retains its
present second recursive child.

The fixture constructs one Below witness from those actual returns. It
invokes mass_lt, budget at one step, and wellFounded. It does not assume
Link or a future execution as a public input. It demonstrates one real local
step. It does not claim an actual infinite or multi-level outer chain.

## Verification

Production strict attempt 1 failed only on the explicit argument shape of
Subrelation.wf. Attempt 2 supplies its implicit endpoints correctly and has
a zero-byte log. The canonical target passes 1787 jobs and replays only the
unchanged old ClosedCompletion unused-variable warning. Kernel attempt 1
checks the actual Below/budget witness. The selected second kernel also
checks mass_lt and wellFounded in that same witness. Both raw attempts
remain present. All eight options are explicit in selected public and
constructed probes. The verifier rejects diagnostics, omissions, printer
failures and any axioms beyond the three standard axioms. Every execution
records effective memory max/high of 4 GiB and zero swap.

No Haskell source, Audit, authority document, old theorem, or old evidence
is changed. The module proves conditional chain finiteness. Actual spine
handoff, native Mu reconstruction transport, all-owner key compatibility,
and the number of all fresh recursive calls remain separate obligations.
