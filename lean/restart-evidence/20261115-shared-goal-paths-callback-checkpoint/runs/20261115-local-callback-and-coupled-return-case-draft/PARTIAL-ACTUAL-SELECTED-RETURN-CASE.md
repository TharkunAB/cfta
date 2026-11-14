# Actual selected return to a nonempty ancestor tail

Status: PARTIAL PROOF. This file is not a Lean module. It does not claim a
completed tuple, row scan or worker theorem. No resource assumption is added
to the four original targets or the prepared16 statement.

The case below allows arbitrary nonempty remaining parent inputs. The inner
row can have arbitrary children and own tries. No child is restricted to a
fallback route. All calls use the SAME supplied workFuel. Source Shapes stay
about the original captured heap and original computed preparedSeed.

## Fixed induction case

Use strong induction on the accepted actual work index. Use the existing
genuine smaller-depth worker IH for captured callbacks. The induction domain
must consist of the literal actual child, row scan, tuple and callback tasks.
It must retain each scope's source origin and actual current prefix facts.
It cannot contain an arbitrary callback program or a future resource field.

The selected-frame case has these actual local names, as in the checked
identity_selected_frame_actual_handoff header:

- previous is the full outer TupleInputs at rowEntry caller/queries/before.
- prepared is the literal CachedOwn.prepare singleton at this row entry.
- history is the current full inner TupleInputs after actual nested children.
- currentFits/currentKnown/currentMass and reserved are the current inner
  source-position conclusions of the smaller actual prefix IH.
- innerSeed, innerMass and innerCount describe that CURRENT position.
- parent, completedPrefix and rest identify the literal deferred parent tail.
- rest can be nonempty. remainingCount bounds its actual length.

At this source return, the checked handoff yields these facts without any
future callback premise:

```lean
  obtain ⟨head, outerPrefix, callbackFits, callbackKnown, callbackMass,
      tailCount, tailReserved, tailIncluded, sourceEquation, endpoint⟩ :=
    identity_selected_frame_actual_handoff formulas solver graph checkEmpty edgesOf
      recursiveDepth workFuel metadata uv limit own innerHeight innerCount innerBound innerMass
      innerSeed parent parentHeight remainingCount parentBound original scopeBefore
      inputs completedPrefix rest caller queries before incoming scs edge residual middle
      staged fragments reached saved after previous member pending prepared history
      currentFits currentKnown currentMass counted reserved

  have smaller := identity_selected_frame_return_steps limit parent completedPrefix rest
    edge residual caller queries parentHeight remainingCount parentBound tailCount
```

The exact actual tail is:

```lean
  let inherited := identity_actual_frame_callbacks graph checkEmpty edgesOf
    recursiveDepth workFuel metadata uv parent
  let tail := identity_actual_parent_tail checkEmpty edgesOf workFuel inherited
    completedPrefix rest
  let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
  let returned := SelectedEdge.finish residual fragment after
  let callbackSeed := advance innerSeed (innerCount * (innerBound + 1))
  let callbackMassBound := innerMass + innerCount * innerBound
  let tailSeed := tuplePlan (nodePlan limit own parentHeight)
    remainingCount parentBound callbackMassBound
    (identity_actual_frame_plan recursiveDepth limit own parent) callbackSeed
```

`tail fragment reached saved returned` is the literal actual parent tuple
program. The existing source equation retains its completed receipt and its
outputs under both completion and stop. It does not replay that tail.

## OPEN proof site 1: the actual smaller task

The next proof step must be an application of the strong IH to THIS source
tuple task, using `smaller` and the derived current facts above. Its required
conclusion is exactly:

```lean
  IdentityEmittedCompleteResources formulas solver reached tailSeed
    (finish uv (tail fragment reached saved returned))
```

The origin must identify the current parent scope, its full original input
list and its source own receipt. The task must use `outerPrefix`, the real
remaining inputs, derived current Packet/Fits/Heap/mass, and `tailReserved`.
The current original-list ledger and packet are conclusions of the smaller
prefix case. They are not new top-level providers.

This application is NOT implemented. The fixed actual source task/origin
family and its joint prefix-resource induction still need construction. In
particular, the current work index proves the strict callback return but
not yet every forward row/tuple entry decrease. A helper that accepts the
conclusion above as a premise would leave this proof site open.

The local native boundary matters. The IH must give Post from `reached`, the
actual tail ENTRY caller, to its actual returned caller. A Post only from
`original` or the oldest captured caller does not imply this local Post.
The new actual captured-callback leaf keeps precisely this local boundary.
It uses the genuine smaller-depth worker at the unchanged workFuel.

## Complete-tail branch after that IH application

The following continuation shows the required native composition. Here
`tailResources` means the result of OPEN proof site 1, not a new premise.
Split the actual tail result. In its complete branch, let the actual observed
equation be:

```lean
  tail fragment reached saved returned =
    NativeContinuations.Result.complete processed outputs finalCaller finalQueries
```

Reduce `finish` in tailResources. Its complete endpoint supplies:

```lean
  Post formulas solver next reached finalCaller final
  final.query = finalQueries
  Fits tailSeed.2 finalCaller.checked
  Heap (fun guard => guard ∈ tailSeed.1) finalCaller.checked.native.machine.heap
```

The head already contains a real Post from rowEntry `caller` to `reached`.
The rowEntry `previous` contains the Packet for the child scan's captured
cache `before`. These are the actual proof compositions:

```lean
  obtain ⟨_headInventory, _headMemos, headPost, _headQuery, _headPacket, _headRest⟩ := head
  obtain ⟨_entryInventory, _entryMemos, _entryPost, _entryQuery, entryPacket, _entryRest⟩ := previous
  have rowPost := headPost.trans tailPost
  have restoredPacket := SourcePruningEnumerationRecursive.captured_post entryPacket rowPost
  have restoredPrefix := tuple_inputs_captured_native_post formulas solver original metadata scopeBefore
    inputs completedPrefix caller finalCaller queries finalQueries before next final
    previous rowPost finalQuery
```

The restored cache is THIS CHILD SCAN'S `before`. It is not necessarily the
oldest root cache. The completed head is not appended to this restored prefix:
the next ordinary alternative starts from the captured prefix that preceded
this child. The native caller and query DO advance to the actual tail end.
The mass of the restored cache is its original captured mass. It does not use
the mutated inner tuple cache mass as a substitute.

## OPEN proof site 2: canonical ordered next-row seed

The handoff already proves:

```lean
  Le tailSeed.2 currentInnerTupleForecast.2 ∧
    tailSeed.1 ⊆ currentInnerTupleForecast.1
```

The actual source-position induction must establish the remaining inclusion:

```lean
  Le currentInnerTupleForecast.2 (seedAt (attempted.length + 1)).2 ∧
    currentInnerTupleForecast.1 ⊆ (seedAt (attempted.length + 1)).1
```

Here seedAt is the ORIGINAL ordered row forecast from the original computed
preparedSeed, scalar limit, guard width, captured ceiling and actual frame
continuation. It is not a newly computed limit from a larger native heap.
The continuation of each scope remains its exact actual frame plan. The root
captured callback uses its own eagerFinal at the genuine smaller worker depth.

This second inclusion is NOT derived in this packet. Static capacity admission
for an arbitrary position alone gives neither this source position nor the
current native fields. Assuming this inclusion externally would leave the
source position generation proof open.

Once produced, compose it with tailIncluded. Enlarge the actual tail Fits and
Heap to the canonical next-row seed. Compose the earlier original captured
Keeps with rowPost.effects.keeps. The restored Packet, query, full prefix and
unchanged captured mass then supply the next actual ordered row case.

## Stopped-tail branch

The SAME strong IH must supply every emitted output under a later stop. The
actual selected callback prepends its receipt and keeps these outputs. Compose
each local OutputResources with headPost to relate it to the rowEntry caller.
No resource obligation is added for the stopped endpoint of the auxiliary
emitted-only predicate. No original noStop outcome or earlier emission is
removed. Original prepared16 and full-history obligations remain unchanged.
