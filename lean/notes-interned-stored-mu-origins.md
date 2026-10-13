# Original calls for stored recursive records

`InternedStoredMuOrigins.Origin` records the actual source expression and
captured environment that created a complete Mu payload. It includes the
ordered depth and ordinary probe calls, the missing canonical key, the
fresh reservation, and the exact normalized body call. It also records
availability of the original captures and the independent source record
invariants before the first probe.

`InternedNestedMuOrigins.build_origins`, `buildMany_origins`, and
`buildEdges_origins` preserve these witnesses through every source
constructor. Ordinary effects introduce no Mu payload. A cache hit retains
the earlier witness. A miss adds the exact original three calls after its
body completes. The proof also covers pending outcomes.

`closed_origins` starts with empty source tables and no external inputs.
It derives origins for every complete stored Mu in that actual run.
It does not assume that the complete run succeeds. `probes_fresh` proves
that the new reserved local is absent from every captured free set after
the two actual probes.

The origin supplies source calls for the general profile correspondence
proof. It does not assert that the original body and probes are equal or
have equal profiles. It also does not prove general first-run completion.

`InternedObservedCleanup` supplies a separate local cleanup law.
`finish_related` preserves empty observations and exact observed output
agreement from paired body observations. `source_finish_related` derives
the fresh-name exclusion needed by the unused-body branch from actual
source execution and `InternedBoundaryFreeAge`. The full constructor
induction must still derive those paired normalized body observations.
