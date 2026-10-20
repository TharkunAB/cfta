# Prefix-only compiler owner attachment: design audit

Status: proposed theorem and proof route only. No Lean declaration or proof was added. No Lean run was made. No repository file was changed.

Reviewed at: 2026-10-20T18:16:05+02:00.

## Result

An exact prefix from a compiled root request is the right input. A completed owner receipt is not the right input. The missing producer must attach the already recovered optional instruction to the actual earlier demand and compiler entry in that same prefix. It must stop at the child return that is exactly the recovered site state.

Existing `NativeMuWriterOrigins.Schedule` and `NativeMuBodyOrigins.Body` contain the right entered body call. Both also require the optional binder and the owner body to finish. The proposed producer must not add either completion requirement.

## Exact proposed endpoint

The following is a mathematical contract. It is not checked Lean code.

Use the existing checked `Trace`. Let `root` be a node request. Fix the already recovered `pair`, `siteBody`, `siteNext`, and `siteBefore`. The public input is:

```text
site : Trace siteFuel
  (.code (requestNode root.domain root.left root.right)) before
  (.code (.optionalBinder pair siteBody siteNext)) siteBefore
```

The target cell, operation result, optional step, and suffix already supplied by OptionalSite/OptionalGeneration stay in the caller's SAME existential. The attachment theorem consumes `site` from that existential. It must not run the locator again to choose another occurrence.

Derive one correlated tuple:

```text
queryFuel, childFuel, queried, queryNext, queryBefore,
handle, chosen, running, captured, first, second
```

Define:

```text
compilerBefore := {queryBefore with native := running}
K result := .finishNode handle result (queryNext result)
entered := Environment.enter compilerBefore.native.machine.domains
  captured.domain.key captured.left captured.right first second
childBefore := {compilerBefore with native := advance compilerBefore.native
  {compilerBefore.native.machine with domains := entered.2}}
```

Retain all these equations and receipts in the SAME tuple:

1. `siteFuel = queryFuel + 2 + childFuel`.
2. `Trace queryFuel (.code (requestNode root.domain root.left root.right)) before (.code (.node queried queryNext)) queryBefore`.
3. `lookupNode width queried queryBefore.native = (.memoized handle, chosen)`.
4. `demandNode handle chosen = (.evaluate captured, running)`.
5. `chosen.nodes.cells handle = some (captured, suspended)` and `running.nodes.cells handle = some (captured, evaluating)`.
6. The actual queried step yields `.code ((compileNode captured).bind K)` at EXACT `compilerBefore`. Retain its actual physical `Inputs`.
7. `decision captured.domain.key captured.left captured.right` is one of `bothMu`, `leftMu`, `rightMu`; hence `compileNode captured = compileMu captured.domain captured.left captured.right`.
8. `identity captured.left = some first`, `identity captured.right = some second`, and `pair = Control.pair first second`.
9. The actual compiler enter step yields `.code (.node (entered.1, body captured.left, body captured.right) (fun value => .optionalBinder pair value K))` at EXACT `childBefore`. Retain its actual physical `Inputs`. These inputs derive `Domain compilerBefore.machine captured.domain` and availability of BOTH captured operands.
10. `Trace childFuel (.code (requestNode entered.1 (body captured.left) (body captured.right))) childBefore (.code (.pure siteBody)) siteBefore`.
11. `siteNext = K`. Equivalently retain the exact whole-control equality if this reduces dependent equality work.

The root prefix, query step, enter step, and bound child trace compose to the given site prefix. The child return state is `siteBefore`, not an independently selected state with an equal heap or body value. Counts record the exact occurrence even when a control or payload repeats.

This endpoint does not require any future owner finish, root finish, native returned cell, or generated-writer premise. The same prefix can be used when the following optional step yields or when that final step blocks. Terminal-step location remains the separate all-outcome locator's responsibility.

## Minimum support layers

The syntactic attachment should first be attempted from the physical prefix alone. This is a design recommendation, not a proved weakening of the current APIs.

- The demand equation itself gives the exact suspended and evaluating FULL captured cells, using `NativeShape.demandNode_evaluate`.
- The executed compiler enter instruction carries physical `Inputs`. Those checks give the captured domain and operand availability at the exact compiler entry. No equality between `queried` and `captured` is required for this layer.
- Initial `SemanticHeap`, if retained from the existing locator caller, supplies pure heap preservation by actual admitted effects. It is not evidence that a code instruction came from the compiler.
- Add initial native `Shape` only if the result must also retain this SAME evaluating owner at `siteBefore`. Propagate Shape through the actual prefix by `DemandMemo.step_preserves`. Then the completed unbound child request is clean, so `DemandRunning.trace_retains` retains the owner from `childBefore` through its actual return. Domain enter leaves the native tables unchanged. This needs no completed owner.
- Equality `captured = queried` is a separate physical-cache claim. `AllocatedNativePhysicalCache.node_started` needs physical `Valid`, current `NodeReady`, and `KeySafe` at `queryBefore`. Actual node Inputs provide the last two facts. They do not provide cache validity. Initial `Good` plus compiled field preservation is one established way to obtain that validity; it is stronger than the syntax-only layer.
- Do not add `History siteBefore`. Existing `NativeEdgeWriterGrowth.History.trace` records completed clean calls. An enclosing owner can still be evaluating at the requested cut. A completed writer at a later captured reader is a later consumer, not a prerequisite for locating this active owner.

## Reusable interfaces and exact gap

1. `DemandPrefixSplit.steps_bind_cases` already splits any actual RAW `Steps` prefix into a nonpure inner prefix or an actual completed inner call followed by its continuation. It retains the exact middle state and fuel sum.
2. `AllocatedNativePhysicalTraceCompletion.Trace.bind` and `AllocatedNativeSemanticTraceReadback.inputs_before_bind` supply the two operations needed for a physical version of that split. There is no public physical arbitrary-prefix `Trace.bind_cases` in the inspected library. Its existing `bind_inverse` is limited to a final pure return.
3. `DemandProtectedPrefix.node_cases` / `edge_cases` already preserve the captured finish handle when a RAW bound-body prefix crosses its return. Their owner-retention helpers use actual completed inner calls; no future owner completion is needed for that part. A physical adaptation must retain each step's actual Inputs rather than reconstruct a separate admitted run.
4. `AllocatedNativeMuSource.enter_prefix` gives the exact entered domain and checked-state update after the literal Mu compiler entry.
5. `NativeObservations.lookupNode_memoized`, `NativeShape.demandNode_evaluate`, and literal native `step` identify the actual owner capture and the protected continuation. A ready hit skips the compiler body. It cannot introduce a fresh optional instruction. A warm CHILD hit is allowed inside the completed child trace.
6. A direct owner branch cannot produce the successful Mu enter. Direct lookup retains the exact original request and requires an absent request key. Both successful Mu identities yield encodable inputs, so `IntersectionFlatMemoKeyDomain.sourceKey_complete` contradicts that absent key. This argument does not need a completed owner or an empty memo table.
7. The remaining substantial induction is COMPILED CONTROL provenance. Follow `compileNode` branches, accepted checked edge `children`, ordered `walk` continuations, and protected finish frames. Split at exact inner returns. If the site lies inside a child, keep that child's actual prefix. If a child already returned, continue through its actual outer continuation at the same state. The root continuation is `.pure`, so a site cannot come from an arbitrary caller continuation.

A private mutual proof over request/compiler/checked-edge/walk prefixes is sufficient. An internal typed frame relation may simplify it. Such a relation must be DERIVED from the root prefix; it must not be an extra public premise that already asserts owner ancestry. Every recursive call can use a shorter actual executed prefix; finite walk decomposition may use list induction. This is not a global execution termination argument.

The inspected completed `Schedule` proof is a useful template for the LOCAL entered-child split after the compiler owner has been found. It does not solve the root-to-owner provenance induction.

## False shortcuts and boundaries

- `Clean` / `BodyCode` prohibit explicit finish frames in source continuations. They explicitly ALLOW optional binders. The frozen actual caller-written fixture has a physically admitted three-step trace and a generated rooted writer, but no compiled root request. Thus Clean, semantic heap validity, or generated writer extraction alone do not establish a compileMu owner.
- Do not select a historical owner by matching the pair, body value, key, or returned value. These data can repeat. The query prefix and exact returned child state must remain correlated with the given site.
- Native shape or matching a truncated memo key does not by itself justify `captured = queried`. Preserve both requests until the physical validity theorem applies.
- `Retained` preserves returned cells and published keys. It does not preserve an evaluating cell merely by definition. Use the actual clean child return and running-cell theorem for that stronger fact.
- Heap Grows, issued-name Extends, physical Publication.History, and native completed-writer History are different facts. None of them alone labels the current compiler continuation.
- Do not return a SAME current compiler owner by completing a different cached query in an independent existential. The proposed theorem retains the exact observed query step and continuation.
- No original program syntax, original capture binding ancestry, unique occurrence, native whole-model termination, or global renewal measure follows from this producer.

## Validation

Read-only source audit. Zero Lean jobs and zero new proof pairs. All source pins are exact current bytes. The proposed endpoint and physical prefix split remain UNPROVED. Existing frozen proofs and fixtures were not changed. The verifier only checks these audit bytes and the cited source bytes.
