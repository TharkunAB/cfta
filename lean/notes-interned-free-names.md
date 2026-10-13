# Full source free names and historical probe boundaries

`InternedFreeNameSemantics` interprets all source Syntax. Ordinary nodes use
the root-profile interpreter to select live edges. Union combines operand
free names. Both binder forms remove the symbolic local. External-name maps
commute with interpretation, including maps that identify captured names.
`InternedFreeNameForm` derives fixed captures and an optional argument.

`InternedNestedFreeNames.build_free`, `buildMany_free`, and `buildEdges_free`
follow the actual source execution. They preserve the decoded free-name
heap and identify each returned free-name set. Complete hits use the stored
probe decoder. Misses use both actual probes and the fresh body call.
Pending outcomes preserve the invariant for every complete record.
`closed_heap` derives the invariant from empty caches. No callback equation
or syntax restriction is assumed.

`InternedSourceFreeNames` derives lexical origins and proves that completed
closed expressions have no free names. Its callback observations include
arbitrary captured probe aliases. Its three-call theorem transfers an old
free-name bound on the actual body to the literal boundaries of both probes.

`InternedFreeNameTransport` lifts arbitrary maps to actual completed source
calls under literal input environments. `build_map` gives exact membership
in the mapped free-name set. `callback_map` gives the same result for every
name other than the target callback argument. The map can identify names;
the theorem does not require injectivity or assume a relation between results.

`InternedFreeNameMuOrigins` retains both semantic tables at the historical
prefix of each stored Mu. `InternedStoredFreeNameBoundary.closed_reference_absent`
therefore gives the literal-boundary implication for every stored Mu in a
closed source execution, even if that execution ends at a pending key.
Fresh Mu-boundary exclusion remains a separate obligation.

`InternedPureProfileIdentity.ordered_identity` proves that equal ordered
pure profiles identify the same available value in a common normalized
state. Set equality is insufficient: the two source unions `[Depth, U0]`
and `[U0, Depth]` have distinct identities in one normalized state.
`InternedPureProfileOrderBoundary` retains the stronger obstruction: two
smart binder bodies with reversed capture order share the same two-probe
key. A later hit returns the first stored order. Thus exact ordered source
interpretation is false. General no-pending still needs actual ordered
replay and the joint Mu-boundary argument.

`lean/repro/PureProfileOrder.hs` confirms both order obstructions in the
current Haskell implementation. The four checks pass in the pinned Nix
environment; see `/tmp/mcfta-20261013-profile-order-source.log`. This staged
open fixture captures the two sentinels explicitly. It does not establish
closed empty-environment reachability or the universal callback contract.

Validation: Lean 4.34.1 completes the full audit with 849 jobs and 33,472
theorem dependency checks. The allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`. This validates the stated theorems;
it does not prove general no-pending or Haskell extraction.

`InternedProbeFreeSupport` transfers interned-name absence through finite
chains of Mu boundaries reached in stored probes. `InternedProbeDependencyAge`
proves those steps strictly decrease the stored Mu identity and gives
well-founded induction. `InternedOldProbeReplay` uses the age bound to
identify the exact probe pair at an old hit from the two local observed
relations. Newer smart hits still need joint body-to-probe boundary transport.
