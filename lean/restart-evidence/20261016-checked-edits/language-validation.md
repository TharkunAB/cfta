# Checked shared edit language validation

Date: 2026-10-16 09:25 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedSharedEditLanguage.lean`.
SHA256: `6b76a581e8d082c3bd4e9167abbc60ca41d7a892fdf232c4c96a7d917f0101ce`.
Length: 304 lines. The source is frozen.

The pinned Lean 4.34.1 focused Lake build passed with 1288 jobs. The only
warning came from the existing unused `inputs` binding in
`InternedFreshOrdinaryClosedCompletion.lean:24`. The new source has no warning.
Raw build output is in `language-build-1.log`.

`language-probe.lean` checked all four public theorem signatures and their
axiom dependencies. It also checked five kernel compositions: actual forest
narrowing, conditional accepted-forest retention, ignored list-root callback,
conditional exactness with the same captured forest, and compiler-derived
lookup conditions. `language-probe-final.log` passed with no warning or error.
The dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

The public namespace is `MicroCFTA.SourceCurrentAllocatedSharedEditLanguage`.
The endpoints are `node`, `children`, `rows`, and `list`. Each endpoint uses
actual new annotated read traces. `list` takes initial readiness, resident
inputs, the selected edit-path domain, valid compiled structure, and valid
initial global memo tables. It returns inclusion in the input forest and
retention under captured-forest acceptance, original `ClassSat`, and the
exact compiled path condition. It does not take a callback language law,
whole-forest closedness, a future cache invariant, or a future result domain.

The mutual proof uses the actual checked leaf receipt for both language
bounds. Ordinary reconstruction uses literal constructor meaning and exact
stored row fields. The recursive branch derives input closedness from the
selected edit domain and uses actual `Head` exactness. Child and row prefixes
use the physical effects of the same read traces. These effects preserve the
returned inventory, loaded fields, equality cache, and current memo tables.

This is a theorem about completed operational read traces. The separate
finite edit theorem constructs those traces from actual-prefix range checks.
No GHC lazy demand schedule, native container representation, or full caller
correspondence follows from this module alone. Literal selection and CAF
forcing adapters retain their previous scope boundaries.
