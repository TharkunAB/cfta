# Real tuple-cons resource step

Status: UNCOMPILED. Root owns compilation and source publication.

The complete private header was frozen before the proof. Its SHA256 is
`8f3df01de11f03070e15c1ff8ff555b8ee18834b175b154e7f60da1674da57d4`.

The theorem proves the tuple-cons case of the exact shared
RealActualSourceCorrectAt predicate. It retains generic Typing, Key,
templates, stop, order, and the actual configured OuterNarrow. It preserves
the original recursiveDepth and workFuel. The conclusion retains resources
for every emitted output, including emissions before a later stop. It also
retains the resources at every complete endpoint.

The only induction premise is the genuine smaller-task hypothesis. The proof
uses actual_source_cons_current to derive the actual head Origin and Current
and their strict work decrease. It passes the same original FrameLedger to
the smaller task. It does not assume child resources, a future callback, a
future FrameLedger, or a future tuple input. The induction premise is the
original strong task induction, not an extra continuation provider.

The proof then uses the actual runtime cons equation and the unchanged
forecast equality. Both equations preserve the complete runtime result.
No output or outcome case is removed. No extra runtime fuel is used.

The root, selected child, and tuple-nil cases remain the other packet owner's
scope. This packet does not claim the whole task induction or real worker.
The original full-worker and finite-witness goals retain their full scope.

## Shared definitions and check layout

This packet does not redeclare the shared predicates. Their authoritative
source is:

`../20261116-current-real-actual-source-tuple-nil-resources-draft/TARGET-DEFINITIONS.lean.txt`

Its SHA256 is
`7bdb6039698e280c6fda08de9db0d5e63c1c193beaeaf6a0fb87f92bec9b2d13`.
It defines ActualEmittedCompleteResources, RealEagerEmittedCompleteAtDepth,
and RealActualSourceCorrectAt exactly once.

For a combined private check, append APPEND.lean.txt after the shared
nil/root packet in the SAME original owner file. Do not append the shared
definitions again. For an independent cons check, use the original owner,
then this PREAMBLE, the authoritative shared TARGET-DEFINITIONS once, this
COMPONENT-HEADER, and this PROOF. Append PROBES.lean.txt after the closing
namespace. The probes have no import lines. No nil/root proof is logically
required for this cons proof.

SOURCE-PINS.sha256 records the original owner and shared interface files.
The proof reuses checked actual_source_cons_current and
actual_source_tuple_cons_run. It also reuses
identity_actual_source_forward_forecasts. No live source was changed.
