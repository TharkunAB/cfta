# Independent review of Scan literal-success alignment

Reviewed on 2026-10-16 at 13:31 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedScanWorkerActual.lean`.
SHA256: `24170d7e672feced01aa0a34b346592a4b9e274637175eb35f30f8cf140e184b`.

No material defect found in `sound`.

The theorem starts with a supplied literal Scan success and legitimate
INITIAL Ready, Values, proper original paths, and fourth-memo Correct.
Its Ranges input is the existing reached-request word-check plan. It does
not supply a completed gate, query, Scan, or suffix; it supplies no final
field invariant, result law, semantic callback, or future Context.

The existing current ClassScanCompletion.finite constructs an actual Scan
from those initial physical conditions. The new graph-to-worker completion
constructs sufficient bounds for that same graph. Both that execution and
the supplied literal success start at the identical Checked state and
fourth memo, with the same original values, class list, and fixed budget.
Unconditional scan_done_unique then identifies the COMPLETE Result pair,
checked return, and saved memo. Product injectivity identifies both the
stopped class and selected list. The proof returns the constructed graph
after those equalities; it does not transfer only its heap or a semantic
property to a different supplied return.

Graph-to-worker completion follows each actual reached branch. The stopped
case uses primary, secondary, seeded, and current conjunction Call bounds
without an induction hypothesis for the suffix. Query and decision read
bounds are combined by maximum. The head-selected case retains its literal
ordered occurrence. No common global native bound or recursive completion
oracle is assumed.

The theorem's conclusion is an actual physical Scan graph. Stronger Context,
input-model, strict Reads, and stopped-language receipts are derived in the
following verified/finite endpoints from their separate legitimate initial
Context and nontrivial-class conditions. They are not silently premises of
this raw alignment lemma. Concrete host demand, memo publication, actual
host global-table events, and unrestricted outer termination stay separate.

This was a source-only review. No source or canonical build was changed.
The separate guard review covers the full Caller and serial integration.
