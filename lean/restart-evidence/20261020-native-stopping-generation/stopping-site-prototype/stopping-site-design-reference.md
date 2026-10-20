# Next native optional-site fixture and stopping extension

Read-only design after the frozen 231-line locator. No new Lean job, production edit or fixture validation belongs to this note.

## Actual fixture design

Use the fixed native Symbol and Guard types. Build the source body `node loop [var 0]` from the empty constructor heap with one input, `reference (intersection 0 1)`. Its availability follows from `reference_available`; intersection references have no interned reservation obligation. The literal completed source build supplies body availability through `build_verified` and its semantic heap through `SourceRecursiveIntersectionSemanticHeap.source`. No full native Good, Fields, allocation certificate or desired occurrence is an input.

Initialize the native memo tables and equality-operation state at that derived heap. Use this caller-written checked control:

```
work (pure ()) (fun _ =>
  optionalBinder (0, 1) body (fun value =>
    work (pure ()) (fun _ => pure value)))
```

The proposed exact trace has three yielded instructions. The first and last primitive jobs are physically admitted pure work. The middle operation binds the free repeated-pair reference under a live ordinary node, so smart construction should install a retained Mu. Compute the actual maybeMu call and selected full result. Prove its key is absent at the trace entry and contains that same full payload at the trace return. Derive the three actual step equations and physical Inputs, then construct the actual Trace. Apply the frozen locator once and eliminate its initial-cell branch with the computed absence. Retain the returned SAME recovered prefix, optional step, checked advance and suffix tuple. Do not construct a parallel desired site or assert that a caller-written instruction has a compileMu owner.

The fixture is not yet checked. Compilation waits for the official locator canonical build. If the candidate does not retain a new Mu, preserve the failed attempt and report the exact computed branch before changing the source.

## Minimal all-outcome extension

The frozen public `trace` covers only yielded instructions. A final blocked optionalBinder can still perform callback work before it returns pending. That work can install a different completed nested Mu before blocking on its own constructor key. Thus an arbitrary selected cell at the full execute stopping heap need not occur in the yielded prefix. This is a semantic possibility, not a new checked concrete counterexample.

The next public endpoint can take exactly:

- `actualInputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before`;
- `semantic : SemanticHeap before.native.machine.heap`;
- an arbitrary exact selected full target Mu at `(execute count control before).state.native.machine.heap`.

It should return the exact initial full cell or one occurrence with `prefixFuel`, `remainingFuel`, pair, body, continuation, siteBefore, a nested maybeMu outcome `call`, and a complete checked step outcome `siteStep`. Retain all of these equations and receipts:

```
count = prefixFuel + 1 + remainingFuel
Trace prefixFuel control before (code (optionalBinder pair body next)) siteBefore
PhysicalExecution.Inputs (code (optionalBinder pair body next)) siteBefore
SemanticHeap siteBefore.heap
Available siteBefore.heap body
maybeMu pair body siteBefore.heap = call
step (code (optionalBinder pair body next)) siteBefore = siteStep
execute count control before = resume remainingFuel siteStep
siteBefore.heap.nodeRecords targetKey = none
call.state.nodeRecords targetKey = some SAME_FULL_TARGET
```

The state and control mapping must remain exact. If `call = done value heap`, `siteStep` is the yielded `code (next value)` with checked state `<advance siteBefore.native {siteBefore.native.machine with heap := heap}, siteBefore.operations>`. If `call = pending pendingKey heap`, `siteStep` is blocked with reason `native (constructor pendingKey)`, the SAME optionalBinder control, and that same exact checked advance. In the latter case `resume` keeps the blocked outcome and executes no continuation. This one resume equation preserves both actual suffix execution and terminal blocking without inventing a successful suffix Trace.

Also retain Grows and issued extension from the original entry to siteBefore, and from `call.state` to the final execute heap. The pending terminal branch has a reflexive suffix. A yielded branch derives its suffix from the remaining actual input plan. Prefix Trace and the current physical input certificate remain explicit; bare physical growth is not an occurrence receipt.

## Proof route and limits

Induct on the actual bounded execute with its physical InputsThrough plan. At count zero the selected cell is initial. At a yielded step recurse on the remaining actual execution. Lift a recovered later site by the exact Trace.cons step and increment its prefix fuel. If the selected cell is already at the current step return, classify that current step. Work adds no Mu by `NativePublicationTrace.work_noNewMu`; all other nonoptional controls preserve the constructor heap. Only optionalBinder remains.

At a terminal done, failed, constraintError or blocked step, classify the actual terminal instruction directly. Nonoptional cases return the initial-cell alternative. A pending optionalBinder recovers the literal maybeMu.pending equation and exact blocked checked outcome from the actual step, including any completed nested cell installed before pending. Physical growth and lookup uniqueness turn failure of exact prior full-cell presence into a literal absent entry key. No empty initial heap or supplied generation property is needed.

The same weak step effects as the frozen locator are sufficient: initial SemanticHeap and current physically admitted arguments give semantic preservation, Grows and issued extension. Existing NativePublicationTrace.execute and PhysicalExecution.through_heap provide the semantic subroute; physical input plans provide actual prefix Trace constructors. The old private step classifier/effects cannot be imported as public APIs, so a new stopping module must either copy those small proofs or coordinate a public helper later. The frozen source must remain unchanged.

This stopping endpoint still does not attach a compileMu owner, recover generated source Written, infer native memo history from physical publication, assert unique occurrence or prove original-program ancestry or termination. The separately developed stopping-rooted writer producer can later consume the SAME maybeMu outcome and selected operation cell. Captured compileMu ownership remains a distinct actual-control provenance obligation.
