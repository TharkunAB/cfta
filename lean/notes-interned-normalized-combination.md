# Retained pending frames with normalized erased source calls

`InternedOuterErasure.OuterErased` protects the local variables introduced
inside a source call. It permits all enclosing inputs to change together.
The source declaration composes discarded empty-child edges through nodes,
unions, and nested binders. `build_outer_erased` derives the exact earlier
result and safe ordinary residual effects for this simultaneous change.
It does not insert intermediate test executions into the source schedule.

`InternedNestedCoherentSites.completed_site_coherent` extracts the actual
earlier completed computation at every declared source site. It also
derives the coherent starting state for that computation.

`InternedNormalizedPreparedSites.Ready` stores these actual earlier source
traces. A normalized leaf can read enclosing variables in its original
syntax. It must structurally erase all such inputs and have the recursively
derived deep-erasure first-completion proof. The earlier lexically closed
leaf cases remain available. `Ready.complete` applies simultaneous erasure
to the real earlier trace and retains later discarded-edge effects.

`InternedNormalizedCombinedConstruction` and
`InternedNormalizedCombinedCompletion` compose these leaves with direct
enclosing-reference retention in one source grammar. A completed depth
trace prepares every nested site before its enclosing Mu reservation.
After reservation, retained references exclude the active keys and erased
subprograms reuse their earlier complete requests. `closed_completes`
starts from empty tables. No ready-state, successful callback, or global
key-stability premise remains in that theorem.

`InternedNormalizedCombinedExamples.program_complete` proves a closed
family at every finite depth, for raw and smart construction. Two outer
binders retain their active references. Their inner subprogram reads both
names and erases them below nested Mu bodies and root self unions. All
edges use symbol zero. `outside_previous` proves that the earlier combined
grammar cannot admit these grandparent-reading inner calls.
`program_not_pending` excludes pending readback for every family member.

A temporary Haskell probe exercised the matching live
`Data.CFTA.Interned` constructors under Nix. All 12 raw and smart cases
with zero through five inner layers completed. They had empty free-variable
sets, exact cached depths, and canonical equality on repeat construction.
The files are `/tmp/mcfta-normalized-combined.hs` and
`/tmp/mcfta-normalized-combined.log`. This finite executable evidence is
separate from the unbounded Lean theorem.

The general first-run closed-input obligation remains open. Each retained
binder in this grammar directly retains every enclosing variable. Each
normalized leaf erases all external inputs. A single request that retains
some active ancestors and erases others needs further source-trace
correspondence. Semantic erasure caused only by union identity collapse or
smart cleanup also remains outside the structural base rules.
