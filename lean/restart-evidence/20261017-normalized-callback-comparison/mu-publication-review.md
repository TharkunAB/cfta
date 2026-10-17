# Actual source Mu publication history

The production source is `lean/MicroCFTA/SourceCurrentNativeMuPublication.lean`.
Its SHA256 is `e24184ee19ac4028a3e1604a82fc3cfea92f4b40d5a8490d08f02143b049efb2`.

## Existing support and new result

`SourceCurrentConstrainedCapSourceHistory.Origin` already retained the actual
Depth, repaired ordinary, and reserved body callback equations. It retained
`Context` and `DepthHeap` at the initial callback point. Its heap producer
retained an earlier first writer. It did not retain the callback execution
histories or a history from empty tables to the earlier writer's initial state.

The new `Publication` retains the literal source, captures, smart flag, three
callback results, all callback states, and the missing key before reservation.
Its `build_done` theorem reconstructs the literal enclosing binder return.
Its `winner` theorem exposes the exact keep-first selection before cleanup.
A later candidate can lose to an earlier stored payload.

`History` is finite data. A publication has three callback histories as strict
subtrees. The reservation occurs between the ordinary and body histories.
`build_history`, `buildMany_history`, and `buildEdges_history` derive histories
from the full repaired executor at every stopping outcome. They require the
existing initial source `Context`. They require no result comparison law.
The mutual producers return `Nonempty History`; `closed_history` selects the
history from the actual empty state.

`History.writers` traces a final Mu record to an initial record or an actual
first publication. `Written` retains the history from the initial state to the
publication's `before` state and all three callback histories. It also requires
that the candidate slot was empty immediately before publication. This last
condition excludes a discarded later candidate. The proof follows any earlier
keep-first winner through the body, ordinary, and Depth histories.
`from_empty` and `closed_writer` exclude an initial-table explanation.
`warm` and `closed_warm` retain the original writer and the exact unchanged
full-state request result. The warm branch does not run the new callback.

## Validation

- `mu-publication-direct-9.source.lean` is the executed final strict snapshot.
  Its log is empty. It is byte-identical to production.
- `mu-publication-canonical-1.log` records a successful single-module build:
  271 jobs and exit 0.
- `mu-publication-public-1` checks 42 distinct public declarations: 22
  handwritten heads, 15 `Publication` projections, and 5 constructors.
  Each has explicit `#check @`, proof printing, and axiom printing.
- `mu-publication-kernels-2` checks two no-premise constructed theorems.
  The nested raw source captures an outer reference. Its returned nested Mu
  has a larger reservation identity than the outer Mu. Both have actual
  source writer histories. The second theorem proves exact full-source warm
  replay and smart readback at the first returned full heap. It supplies a
  callback that would be pending if executed. The hit returns the earlier
  selected record and retains its callback subhistories.
- All selected probes use the eight explicit printer/linter options, including
  `pp.proofs.threshold 254`. Their only axioms are `propext`,
  `Classical.choice`, and `Quot.sound`. They have no diagnostics or omissions.
- Every selected Lean job reads back effective cgroup limits:
  MemoryMax = 4294967296, MemoryHigh = 4294967296, MemorySwapMax = 0.

All numbered source and raw log files remain present. Direct attempts 1, 2,
4, 5, 6, and 8 failed. Attempts 3 and 7 checked earlier partial sources.
Kernel attempt 1 has the warm-equality diagnostic and an observed SIGTERM
exit (-15) during later proof printing. Its exact emitted 8192-byte log and
source remain preserved. The termination cause is not established here.
Kernel attempt 2 fixes the equality and uses private checked proofs with
public aliases for bounded proof printing. Only attempt 2 is selected.

## Boundary

This module proves a causal publication history, not normalized callback
comparison. It assumes neither body/ordinary equality nor an unused-Mu output
law. Entry identities do not serve as publication time. Histories retain Mu
publication dependencies; `retain` records the absence of new Mu payloads.
They do not expose a global instruction event count or a trace for every
constructor instruction. The separate normalized comparison must derive its
candidate law before publication and use the produced earlier-winner history.
