# Private support terms and labels

`SupportTerms` follows `Gen.Label.surface`, `applicationTermChildren`,
`applicationLeftChildren`, and `labelTermWith` with the standard `Label`
representation. `GeneratorCombinators.Label` includes every private source
constructor. User labels remain a separate constructor.

`applicationLeft_surface` and `application_surface` prove that spine
recognition preserves the complete ordered user forest. `label_surface`
proves that closing a layer retains this forest under one user constructor.
It covers n-way joins, choice wrappers, pure, application, and the default
single-child wrapper. A private `Pure` term must be nullary. The source creates
such terms, and `pure_valid`, `apply_valid`, and `choice_valid` preserve the
invariant for the corresponding constructors. The raw exported term helper
does not validate arbitrary malformed private trees.

`label_select` preserves each member position and mass. `label_values`
preserves the complete decoded-value distribution. The adapter pays one unit
of size, as `labelStaticMatching` does. `surface_not_injective` proves why the
user projection must not be treated as a distinct-member index.

The support graph builder and term callback must choose the same root case.
This module does not yet prove that correspondence for every imported graph,
recursive graph, or heterogeneous recipe. It verifies the term callbacks and
projection rather than assuming their desired effect.
