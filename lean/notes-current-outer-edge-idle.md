# Initial facts exclude every outer edge memo diagnostic

Proof checkpoint: `dce1e970`. Source main: `c0cc8a05`.
Starting local checkpoint: `cf7d6049`.
Evidence: `restart-evidence/20261018-outer-edge-idle/`.

Initial semantic facts, scheduled capacity and an initially idle edge table
exclude every edge memo diagnostic in all six outer phases. No lower-fuel
ceiling or successful outcome of the enclosing call is required. General
node-owner exclusion and successful termination remain open.

The existing `SourceCurrentOuterEdgeIdle` already proves that an idle edge
table stays idle on successful returns and cannot report a busy edge fault.
That module remains unchanged. An edge body calls Parent without an outer
recursive call. The edge owner finishes before descendants start. Node
owners can remain evaluating across recursive descent.

`SourceCurrentOuterEdgeIdleReached.step` and `reached` apply that existing
result to exact literal outer prefixes. They use actual completed edge,
descendant and node equations for earlier siblings. Other steps retain the
edge table. These theorems need no semantic invariant or resource premise.
They concern reached phase entries. They do not concern the internal or
terminal state of a failing Parent call.

`SourceCurrentOuterEdgeMemoFailure.failed` starts with a literal edge memo
fault. Its six-phase induction derives the exact reached nonempty row entry
and failing edge call. It retains the complete original suffix, the current
caller, handle, observation and final caller. It assumes no supplied graph,
semantic invariant or idle table.

`SourceCurrentOuterInitialEdgeMemoFailure.edge_no_memo_failure` uses valid
key links to exclude an absent edge cell. Edge idle excludes busy. Ready
returns cannot fail. The evaluate branch can report a Parent diagnostic,
but cannot report an edge memo diagnostic. It keeps the actual captured
owner. It does not replace that owner with the current candidate.

The global `no_edge_memo_failure` theorem applies InitialPrefix.reached to
the derived row entry. Its current Context supplies memo validity at that
exact caller. The new reached theorem supplies edge idle there. Their
combination excludes every edge memo observation. Initial Context, Frame,
Fits, raw guard carrier, ready inputs and scheduled Room remain explicit.
Actual completed earlier siblings supply their own semantic receipts.

The integration constructs a root with constrained recursive Mu children.
It derives its own allocation history, Context, Frame, Fits, raw carrier,
inherited readiness and computed mathematical Room. Its outer fuel is 2.
With all lower fuels 0, it reports a Parent fault. The exact terminal edge
owner remains evaluating. The failing edge call's reached row entry is
edge-idle. For the same root and any lower fuels, the new global theorem
excludes every edge memo diagnostic. The selected recursive child lies
outside every finite Plain Cap. No whole successful run or practical host
width is asserted.

Three production strict logs and the integration strict log are literally
empty. All five public, one constructed and one private full statement,
proof and axiom pairs pass in five groups. They use all eight settings and
only propext, Classical.choice and Quot.sound. Full Audit passes 3265 jobs
and 71327 checks. Canonical logs retain only the existing baseline warning.
Every job records 4 GiB maximum/high and zero swap. Closing peaks are at
most 381 MiB.

The first root strict attempt exited zero with three warnings. Its raw
log and canonical receipt remain unselected. The final source moves the
equality instances below the private helper and removes a redundant simpa.
The selected second strict log is empty. The theorem and its assumptions
are unchanged. The edge dispatch producer also retains its first failed
elaboration attempt. No warning or error is suppressed.

The next main target is actual source-anchor production for node requests.
NativeQueryRowOrigins still has explicit Mu and union residual branches.
These branches need the actual captured writer's rows, reconstruction and
ordered child calls. Then compose through ClassFoldRowOrigins, Parent and
the actual walk dispatch. Existing positional mass descent is conditional
on an exact anchor handoff. It does not produce that handoff for runtime
requests. The same original value can recur with a different inherited
identity, so strict original-value descent is not a general rank.

Read [the independent review](restart-evidence/20261018-outer-edge-idle/edge-idle-review-report.md) for the exact next-producer map. General
used-binder writer alignment must retain its complete source scope. The
existing BinderFree comparison is not a general used-writer proof. Prove
impossible closed-input branches instead of assuming their origin.

All-ancestor node-key exclusion and a finite fresh-call bound remain open.
Even complete collision exclusion does not alone prove termination.
Repeated-pass convergence, equality-operation resources, host Int adequacy
and public Haskell correspondence remain separate obligations.

No Haskell source changes in this checkpoint. No new executable defect is
claimed. FINDINGS keeps the external repair registry first. Field-pool
repair `b9219b9e` remains fixed in `c0cc8a05`. All earlier proofs, repairs,
counterexamples and marked drafts remain unchanged. Publication awaits
the existing direct approval. The full-library goal stays active.
