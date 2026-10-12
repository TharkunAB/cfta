# Recursive member boundaries

A second support comparison found a defect in single `recur`. Consider
`recur (oneof [pure 0, node "s" self])`. The support closes an unresolved
recursive reference by wrapping it as one child. The term decoder instead
runs `labelTerm` on the complete selected recursive term. It removes that
term's private choice and pure roots. The first positive-size term then has
no child under `s`, although the graph requires one.

`RecursiveSupportBoundary.decoded_not_accepted` proves the old mismatch.
`same_surface` proves why value and user-surface checks can miss it. The two
engine structures can have the same user projection. The source probe is
`/tmp/microcfta-recursive-support-conformance.hs`.

The repair adds a private `Recursion` label inside the recursive binder body.
The support, inspection, and term fixed points use that same boundary.
Inverse ranking removes exactly one matching wrapper. The boundary remains
present after conversion to a bounded static source. A parent constructor
and an application spine therefore treat a recursive member as one complete
child. Grouped recursion already has an opaque AtKey/Family boundary.

The public engine terms change shape. `surface` removes the new private
wrapper. Values, counts, masses, size classes, and member rank order retain
their definitions. The new constructor does not pay a size unit in the original generator.
Importing the raw support through `fromAutomaton` counts every private root
as an ordinary graph node. Bounds for that separate node-count language can
therefore increase. The retained import fixture changes its bound from 6 to 8.

`wrap_injective` and `unwrap_wrap` prove exact wrapper identity and inverse.
`label_wrap` and `spine_wrap` prove the corrected parent behavior.
`surface_wrap`, `wrapped_values`, and `wrapped_select` prove preservation of
user projection, decoded-value distribution, rank positions, masses, and
member sizes. `support_wrap` proves the matching graph language.
`selected_accepted` proves every member of the repaired example's recursive
stream is accepted. The general heterogeneous recursive-record adapter
still needs its correspondence to these local boundary laws.

Validation uses the existing generator suites and direct support/inspection
acceptance checks. The current validation results are in SYSTEM.md.
