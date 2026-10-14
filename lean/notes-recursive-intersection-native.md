# Compiled source branches and resumable native memo execution

Proof checkpoint: `2b6b1e2a`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Operations.hs:intersectOpen`, `intersectOpenEdge`, and
`Interned/FlatMemo.hs:lookupOrInsert`, `insert`, and `write`.

## Exact branch compiler

`SourceRecursiveIntersectionCode` retains explicit constructor work, domain
entry, original physical binding reads, optional-binder construction, recursive
node and edge requests, and memo completion frames. Each instruction keeps
its continuation. `interpret_bind` and `interpret_walk` derive exact source
result sequencing and ordered stateful calls, including failed caches.

`SourceRecursiveIntersectionCompile.compileNode` compiles every physical
guarded branch. It preserves empty/reset/self/swap/cutoff order, actual Mu
body requests, canonical domain entry, ordered unions, original free-binding
reads, and the symbol hash join before canonical node construction.
`compileEdge` checks arity before child requests and retains child order,
literal symbol, conjoined guard, and the source empty-edge mismatch case.

`compileNode_exact` and `compileEdge_exact` prove equality with the existing
guarded kernel for arbitrary recursive node callbacks. Complete machine
effects and failures agree. No purity or product-language law is supplied.
The interpreter uses the kernel edge worker for the source comparison.

## Recursive native driver

`SourceRecursiveIntersectionNative.step` interprets the compiled code with
the separate typed node and edge memo tables. Every recursive instruction
uses those tables. A node placeholder retains the source direct-call bypass.
A miss publishes its original suspended thunk, marks it evaluating, and then
expands the compiled body. A completion frame updates that original cell.
A completed hit enters the original continuation without effects. A busy hit
retains its recursive instruction and current caches as a blocked observation.
It does not become Empty, a cutoff reference, or a completed result.

`execute` uses a finite step bound. Zero fuel yields the original remaining
code and exact state. `execute_add` and `yielded_resume` prove that a yielded
run can continue with more fuel without restarting its source effects or
discarding its memo cells. Completed and blocked observations remain stable
under additional fuel alone. A blocked observation requires a relevant state
change before retry. This model does not specify GHC thread scheduling.

`SourceRecursiveIntersectionNativeRequests` derives exact miss, hit, busy,
and bypass steps. Checked available source requests preserve both memo
invariants through lookup and demand before their compiled bodies run.
Machine word bounds remain explicit. No global supply-overflow result is
added.

## Continuations, traces, and physical effects

`SourceRecursiveIntersectionNativeContinuation.step_bind` proves that one
native step preserves an appended outer continuation. This includes both
recursive memo families and pending constructor observations.

`SourceRecursiveIntersectionNativeTrace.Steps` records actual yielded steps
and exact intermediate caches. `Steps.execute` and `execute_steps` connect
these traces to bounded execution in both directions. `Steps.trans` composes
traces at the preceding returned state. `Steps.bind` retains each step under
an outer continuation. `done_trace` derives a finite trace to the returned
pure value from an actual completed run. `trace_done` derives completion from
such a trace. Neither theorem asserts that every native request completes.

`SourceRecursiveIntersectionNativeEffects` proves source work and canonical
domain entry retain both pending memo families. Optional-binder completion
uses its exact returned source heap. Pending construction retains the actual
installed key, new heap, and original continuation. Actual constructor
verification derives memo invariant retention for these physical effects.

## Next obligations

Actual completed runs now derive finite nested evaluations, and those
evaluations construct the converse exact native runs. Trace splitting retains
the original body, shared state, continuation, and total step count. Source
body compilation excludes native completion frames. Completed source bodies
retain both memo structures and every enclosing running cell. Their original
completion frame stores the actual returned value in the original cell.
Read [native completion](notes-recursive-intersection-completion.md).

Derive full guarded kernel correspondence and semantic `Produced` from these
actual evaluation trees. Structural `Shape` and frame retention do not supply
that provenance. Carry explicit word bounds and derive physical/domain facts,
availability, exact growth, and finite child bounds. Do not supply provenance
at completion frames, assume purity, or replace native body execution with an
uncached callback. The old completion helpers still use uncached body premises.

Then derive the physical input view, finite reachable payload inventory,
sufficient first-run bounds, and `ProductReadback.members` and `.rejected`.
`product_exact` gives product language after those obligations. General open
nested first-run constructor completion, new-body preparation, concrete GHC
primitives and scheduling, and verified Haskell extraction remain open.
The exact Sized source paths and cold-table results remain unchanged.

## Validation at this checkpoint

All seven new modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,235 jobs and 40,978 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-native-driver-20261014-audit.log`.
No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. Prior proof, draft, and fixture bytes remain preserved
against the saved manifest.
