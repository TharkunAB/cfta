# Actual checked contextual completion

Validated 2026-10-16 06:02 CEST. Source files are frozen at the hashes in
`allocated-native-contextual-sha256.txt`.

## Result

`SourceCurrentAllocatedNativeContextualCode.Certified` records local code
continuation laws. Primitive branches use literal returned machines. Node
and edge continuations receive the law for the exact child request. An edge
request also retains matching symbols. The predicate does not assert an
execution or a completed result.

`SourceCurrentAllocatedNativeContextualCompletion` derives actual checked
completion and contextual laws jointly. `Receipt` extends the existing
physical trace receipt. It also records final `Contextual`, final
`SemanticReady`, and the local returned law. The trace, physical effects,
returned value, and semantic law refer to the same actual checked states.

The private `all_bodies` uses strong induction on independent `requiredFuel`.
The current native lookup/demand branches identify the exact original
request. A ready hit uses physical validity and the initial contextual
cache. A miss derives the child body law before its finish. The actual
body trace retains the evaluating frame. The finish stores that derived
law. All recursive body callbacks and all static source certificate
interfaces are discharged internally by `source_bodies`.

Public endpoints are `node_complete`, `edge_complete`, `request_complete`,
`edge_request_complete`, `initial_complete`, and `cold_complete`.
`Receipt.done` erases each receipt to literal checked completion.

`initial_complete` takes a fixed original input model, ranked input model,
and admissible contextual warm cache. Original closed inputs derive the
pure schedule and active bound from initial idle cells.

`cold_complete` derives both input models from actual available original
closed inputs. Empty native memo tables derive contextual validity and
idle state. It returns one actual checked receipt, final idle state, and
for every ambient environment and finite term:

    meaning result term <-> meaning left term /\ meaning right term

It does not assume a local parent law, `FinishThrough`, old eager execution,
`NodeProduced`, a completed recursive callback, final field availability,
or a final semantic heap invariant.

## Initial premises and scope

- `Good` includes physical native cache validity, required heap readiness,
  operation-cache validity, and successful same-cache equality field loads
  for resident edge keys.
- `SemanticReady` includes the actual guarded and budget heap invariants.
- General recursive endpoints retain original source scope, independent
  pure-schedule completeness, current ready operands, source heap growth,
  issued history, active-frame bounds, and reached `WordRanges`.
- The initial endpoints derive pure completeness and active bounds. Actual
  reached `WordRanges` remain explicit. No fixed machine-width capacity or
  range construction is proved here.
- Warm contextual cache admissibility is an explicit initial premise.
  The cold endpoint derives it from empty native tables.
- Rejected and mismatched checked edge bodies retain their real sentinel
  allocation and skip child requests. Accepted bodies use actual loaded
  constraints and literal conjunction readback.
- Result free-list closedness is not concluded here. Independent language
  exactness does not prove that metadata fact. A separate scope companion
  remains relevant for query closure.
- These proofs concern the actual checked Lean interpreter. They do not
  prove GHC evaluation order, pending thunk publication, physical container
  representation, or end-to-end lazy source/runtime equivalence.

## Validation

Focused canonical commands:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextualCode
    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion

Both finished with exit 0. The final completion target passed 1116 jobs.
There are no new warnings. The existing unused `inputs` dependency warning
was replayed.

Direct public checks:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-recursive/allocated-native-contextual-completion-probe.lean

This finished with exit 0. Eight public axiom checks and eight signatures
pass. Every axiom is in `propext`, `Classical.choice`, or `Quot.sound`.
Three kernel examples consume the public API: exact receipt erasure and
physical plan, cold exact language plus arbitrary extra fuel, and actual
edge lookup/demand/finish with its derived contextual law.

Only the two new owned proof files and new evidence files were written.
No prior proof source, Haskell source, Audit, documentation, or Git state
was edited by this task.
