# Completed-build structural row prototype

This prototype remains in `/tmp/mcfta-build-structural-row-origins/`.
It does not change repository source, Audit, documentation or build artifacts.

`build_row_origin` consumes the actual completed repaired `build`, its historical
`ConstrainedCapSourceHistory.Context`, and the exact structural `RowAt` row.
It derives `SourceRow` by induction on source syntax size. Only the union case
recurses, through the actual selected original member call.

The node alternative keeps different canonical output and original source
indices. The existing `RowCall` retains the source `EdgeSyntax`, complete symbol
and guard, ordered child values, actual `buildMany` and `makeEdge`, exact row
prefix and suffix, context, and growth into the node result heap. Its output is
the same complete row selected in the normalized node.

The capture alternative keeps the exact variable slot and captured value.
The binder alternative keeps both actual callbacks, the actual request, the
selected complete Mu cell at its actual return heap, the exact smart finish,
and the same structural row in that selected stored body. It covers cold and
warm selection, raw binders, smart-unused cleanup, and retained used binders.
The bare-self cleanup cannot supply a row. No current-callback body equality
is asserted for a warm selected winner.

The union alternative keeps the same source/value index and exact original
`buildMany` prefix, selected call and suffix. Root normalization inversion
uses literal ordinary rows or whole opaque Mu atoms. It does not unfold Mu.

Selected strict receipt: `prototype-direct-4`, terminal 0 and zero log bytes.
Selected readback: `prototype-public-1`, terminal 0 and full two public heads,
all eight printer options, no omissions, and only the three standard axioms.
All five Lean runs use pinned 4.34.1 with the 4 GiB hard/high cap, zero swap,
and a five-minute wall cap. The selected strict run used 170 MiB peak.
Attempts 1–3 remain present. They contain parser, index-inference and proof
elaboration errors. No attempt timed out or reached the memory cap.

This is a checked prototype, not an installed canonical module. No constructed
integration is claimed. The parent will own official source and canonical
build. Remaining work includes capture binding provenance, causal selected
writer/source ancestry, and a sound global renewal argument. A structural
value `RowAt` does not give strict original syntax descent across those arms.
