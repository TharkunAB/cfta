# Independent review of actual reduced-edge calls

Reviewed on 2026-10-16 at 11:18 CEST. No material defect found.

## Exact supplied return

`SourceCurrentAllocatedPartialEdgeActual.edge_body` consumes the strict
`PartialSourceReads.EdgeBodyReads` indexed by the supplied `EdgeBody`.
The same parent reads reach both `ParentEdgeActual.verified` and
`ProbeParent.parent_heap` (source lines 63–90). Thus the receipt, final
three-family bundle, and probe heap refer to the supplied result and
complete returned state. The proof does not substitute a different
existential parent execution.

The body derives its `EdgeLaw` from the actual parent receipt and the
literal input edge readback. Its semantic law is not a premise. Initial
`Sound`, physical `Ready`, inventory admission, fourth-memo correctness,
merge cache coverage, global coherence, and probe heap remain explicit.
Initial `Sound` permits already completed warm cells with established
laws. It does not require a result law for an evaluating cell.

## Exact evaluating owner

`edge_call` uses the actual `beginEdge` equation to obtain the original
running request, cell, and physical key (lines 119–135). The body retains
the entire edge-result table. This retains the same evaluating owner at
the same handle. The proof derives the owner law before `finishEdge`,
then applies `EdgeLaw.of_key` to the actual candidate (lines 136–149).
The latter uses coherent resident edge identity and ready inherited
physical equality keys. It does not assert equality of arbitrary raw
records. Finishing retains the actual checked state and body probe heap.
The returned receipt retains node cells and the actual merge/fourth
history. Its global validity refers to the supplied final bundle.

The hit branch obtains whole-state equality and the proved warm law from
the actual ready observation (lines 109–118). It does not run the body.
No completed trace is constructed from a busy observation.

## Reached checks and limits

The current `Ranges` starts with raw contradiction being false, then the
literal successful field load (lines 32–44). Thus raw rejection does not
require Scan ranges. `CallRanges` asks only about an actual evaluate
observation. Neither condition supplies a completed body or a semantic
answer. The theorems still consume an actual finite strict read schedule.
They do not prove general mutual caller completion or preservation for
all recursive node branches. They do not derive strict schedules from
historical unanchored primary reads. No GHC thunk forcing, publication,
concurrency, physical hash-table, or machine identity adequacy is claimed.

## Independent checks

Command:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-caller-invariants/partial-edge-actual-public.lean
```

Terminal exit: 0. Two requested public axiom checks and full signatures
pass. Three external kernels also pass:

1. `same_owner` combines the actual evaluated call receipt, final probe
   heap, and exact returned owner cell at the supplied finish state. Its
   owner and evaluating cell are derived from the initial actual start.
2. `rejected_ranges` proves raw contradiction makes the range plan
   vacuous.
3. `body_table` proves every supplied raw edge body preserves the whole
   edge-result table before its own finish.

All five axiom probes report only `propext`, `Classical.choice`, and
`Quot.sound`. There are no errors, warnings, or `sorryAx` entries. The
printed signatures have the expected concrete alphabet/guard instances,
width, initial invariants, actual trace, and supplied read indices.
No canonical build was run by this reviewer. No proof source was edited.
