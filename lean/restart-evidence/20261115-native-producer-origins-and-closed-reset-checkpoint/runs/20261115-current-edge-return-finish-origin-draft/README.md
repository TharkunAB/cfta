# Actual edge return finish origin

Status: UNCOMPILED candidate. Root owns strict Lean validation.

SourceCurrentAllocatedNativeEdgeReturnOrigin.returned_edge_cell_finish_prefix
extracts the actual finish that produced a returned edge cell in ONE supplied
checked Trace. The trace starts with Native.initial width machine. BOTH
complete native memo families are empty. It retains original count<=fuel.

The result contains the SAME edge handle, complete captured EdgeRequest and
whole returned EdgeValue. It constructs an original indexed prefix to the
actual finishEdge instruction, the evaluating owner cell, the real one-step
finish, exact installed returned cell, full operation/native states and literal
suffix to the SAME final control/state. Prefix+1+suffix=whole count. The prefix
is strictly below the whole count and original supplied fuel. The final control
can be incomplete. No termination or later completion is assumed.

The four generic private backward lifecycle proofs are byte-exact copies of
the checked node packet. None of those helpers is public, so this packet does
not export or depend on their private names. Typed edge lookup/demand inversion
uses the actual edge family. Node lookup/demand instead retain the edge cells.
The checked edge demand branch uses SourceEqualityNativeDemand.step directly;
it does not substitute the older eager edge compiler. The successful node raw
source and all old public headers remain unchanged.

The receipt proves a same-trace finish event. It does not identify an earlier
compileEdge/allocated edgeBody dispatch for arbitrary initial Code. Actual
compiler ancestry is separate work. No future Good, physicality, extension,
model, admission, semantic cache law, source/result supplier, Clean, or Fields
premise is added. The actual Trace retains its genuine step input checks.

The original full native C/M target and SAME-root finite accepted compatible
witness remain open. No Haskell defect or fix was found. No compiler, live
Source, Git, board, runtime or /tmp operation was performed.

PUBLIC-HEADER.lean.txt was frozen first and matches the raw declaration exactly.
PROBES.lean.txt has appendable commands only. SOURCE-PINS.json and MANIFEST.sha256
record inputs and packet bytes. Keep any failure log; repairs use a NEW packet.
