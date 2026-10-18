# Positive projection source-route review

Reviewed 2026-10-18 23:46 CEST. Production SHA `37141d118ba5ebaae46d063873a687d0bb825123d274d43355c0ca9b96fac1d0`.

`Route` (line 40) follows the signed projection path through indexed rows and
literal ordinary children. Its root constructor selects the same complete
physical row. `Route.mass_lt` (line 51) proves strict structural mass decrease
from this operand to every child in that endpoint row.

`positive` (line 379) consumes an actual historical false primary `NodeTrace`,
initial semantic readiness, initial `UnionNormal`, initial operand availability,
and growth from the gate return to the projection entry. It also consumes the
projection entry's semantic and cost heaps, operand availability, causal plain
guard heap, exact completed `Project` graph, and selected non-plain physical
row. It returns `Route` for that same operand, path, and row.

The proof derives a path certificate from the actual primary trace. The finite
shortcut uses `RequiredFiniteExposure.ordinary_of_zero_closed` (lines 40–49).
That helper needs literal union irreducibility. `SemanticReady` does not contain
that field, and this component does not prove it from semantic readiness.
`RequiredUnionNormal.build` (line 125) derives it from actual source construction.
The fixture uses that producer. This is an explicit additional initial invariant,
not an assumed future projection result.

The accepted Mu cases use `GatePlainRegion.annotations` (line 53). Actual open
row and Head reads use `ConstrainedCapOpenExposure.nodeEdges` and `.head` with
the produced causal Mu guard store. The zero local cap is derived from the
accepted annotation; no source fragment or finite-cap input restriction is
assumed. The projection induction uses its actual ordered child, union-read,
and Head graphs. It derives semantic/cost/guard facts at their intermediate
heaps. A plain recursive region cannot supply the selected non-plain row.
No blanket plain annotation on all stored edges is assumed.

The constructed source has two original rows. One child is a closed used Mu
with a plain recursive row. The other is an ordinary positive equality row with
two finite children. An actual false primary `[0]` trace visits both children.
The literal cold projection returns two physical rows. Production `positive`
recovers the positive row through the ordinary branch. Production `mass_lt`
proves the chosen continuation is smaller than the original projection operand.
All source, initial invariants, actual calls, and selected records derive from
this fixture's own build. The public theorem has its full statement and aliases
a private checked witness. It does not claim finite inhabitation of the Mu.

Selected checks are `projection-direct-3` and `projection-kernels-direct-3`
(literal zero-byte logs), `projection-canonical-1` (terminal zero, 1138 jobs,
only the known older ClosedCompletion warning), `projection-public-1` (full 3),
and `projection-kernels-public-1` (full 1). Both full groups use all eight print
and linter settings, show signatures, full proofs, and axioms, and contain no
printer omissions. Only the standard three axioms occur. All jobs record
4 GiB maximum/high memory, zero swap, and a five-minute cap.

All failed attempts remain. Production attempt 1 had constructor documentation,
instance alignment, placeholder, and elaboration errors. Attempt 2 had two
remaining elaboration errors. Attempt 3 is selected. Fixture attempts 1 and 2
failed to expose concrete root and Mu shapes to gate constructors. Attempt 3
normalizes only those concrete value arguments and is selected. No attempt
was interrupted or omitted.

The route begins at the projection operand, which may already contain earlier
edits. This does not identify an initial outer input occurrence or relate
native result children to proper children of both query operands. Full selected
renewal through native queries and Mu, physical key exclusion, a finite fresh
call bound, general completion, and Haskell correspondence remain separate.
