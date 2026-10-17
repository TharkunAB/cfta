# Actual checked root-query row origins

The source is `SourceCurrentNativeQueryRowOrigins.lean`. Its SHA-256 is
`93af295d449b1bdf0b35613a3e45597adb4a4086a7d20ce5a70eee1502fa7ec3`.

## Result

`request` consumes an actual completed CHECKED node request, initial `Good`,
initial causal native `History`, closed operands, and an indexed selected
output row. It derives the final history, final `Good`, actual heap growth,
and `RowOrigin`. It does not require a final writer, an internal history,
a caller-supplied compiler decision, or a `compileRows` trace.

The proof finds the actual captured returned cell. It follows literal swap
and reset bodies, including earlier warm winners. Each `Route` step records
the actual compiler trace and forwarded request. A finite reset/order measure
strictly decreases. Reset clears the domain reset test. A swap reverses the
actual keyable operand comparison exactly once. Final-reader history and
returned-cell retention supply every earlier captured writer. A route records captured request dependencies, not a concatenation of chronological subtraces. A warm child writer can precede the requesting caller. Each hop retains its own literal body trace and final-reader retention evidence.

At the terminal request, self returns the literal input row at the same
index. Ordinary compilation derives both original row indices, symbol
agreement, the exact full joined guard, and the actual retained edge
`Written`. The proof includes zero-child rows. Empty, repeated-reference,
and unsupported branches cannot return a selected ordinary row.

Mu, union, and reference source branches remain explicit `Residual` cases.
The result does not supply their Head/reconstruction row origins. It does
not prove full class/edit persistence, new guard-only class origins, or
outer termination. `RowOrigin` is a classification with this residual case.

`returned` is the completed-cell helper. `leaf` consumes existing actual
shared-leaf `Reads`, initial history, a closed input, and a selected output
row. It derives the exact historical target force, checked query receipt,
advanced shared state equation, final history, and the query row origin.
It does not ask the caller to supply that target or its query lineage.

## Trust boundary

`PhysicalTraceCompletion.Trace` includes literal transitions AND per-step
physical `Inputs`, including key bounds and protected finish checks. The
public producer verifies this CHECKED trace. It does not derive those
checks from a bare worker `execute` equation. Existing leaf `Reads` also
records completed actual components. Neither endpoint is a new general
initial completion theorem. Closedness is local to the two query operands;
no whole-forest closure, finite Cap, or desired row law is a premise.

## Constructed checks

The fixture builds an actual original container whose children have rows
`{a,b}` and `{a,c}`. All rows have zero children. It derives physical and
semantic readiness from that source build and prepares the actual top
constraint field. An existing initial finite ordinary producer constructs
its own CHECKED cold query. A separate literal execution identifies the
singleton `a` result and complete returned state. The new producer derives
its `RowOrigin` and full-guard `Joined` writer. The fixture then constructs
a literal one-step warm request from the published returned cell and proves
both origins again at the same full state. No future query, graph, or
output-origin premise is supplied.

A second source-built query takes the first original child twice. It
constructs its own checked execution, proves the selected self branch,
retains the literal source row, and obtains its captured node writer and
new `RowOrigin`. This check is separate from the zero-child joined case.
There are two constructed public statements. The shared-leaf adapter has a
full imported proof check; this component adds no separate leaf fixture.

## Validation and retained attempts

The selected production strict check is `class-origin-direct-6`: terminal
zero, genuinely zero log bytes. The selected canonical run is
`class-origin-canonical-2`: terminal zero, 1413 jobs. Its only warning is
the unchanged imported `InternedFreshOrdinaryClosedCompletion` warning.
The owned source has no warning. The selected public group prints all
8 handwritten heads plus both public `Route` constructors (10 pairs).
Every selected print group sets `linter.all` and all seven proof-print
options, uses `#check @`, prints the full declaration, and prints axioms.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

All earlier attempts remain. Direct attempts 1, 3, and 4 failed during
proof elaboration. Direct 2 and 5 terminated zero but had linter warnings;
they are not selected as strict-clean evidence. Canonical 1 replayed the
private unused-instance warning and is superseded by canonical 2. Kernel
attempt 1 failed at explicit key-safety witnesses and request projection
rewrites. Kernel 2 passed printer-free. Kernel 3 is the selected printer-free zero-byte check. It retains the same two explicit public types and places their computed proofs in private checked witnesses. The first full fixture print terminated with signal 15 and retained its partial raw log; it is not selected. The replacement prints the exact public witness aliases without expanding the private computed proofs. These
failures do not establish a counterexample or an implementation defect.

Every Lean run executes its own immutable absolute snapshot with the pinned
4.34.1 toolchain and `-Dlinter.all=true`. The inner worker reads its actual
cgroup limits. Every recorded run has MemoryMax=MemoryHigh=4294967296 bytes
and MemorySwapMax=0. No old production source, Haskell source, Audit file,
or authority document was changed by this component.
