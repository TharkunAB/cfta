# Independent reduced-edge call review

Reviewed SourceCurrentAllocatedPartialEdgeCall against its frozen dependency
definitions and cfta/src/Data/CFTA/Equality/Operations.hs:150–168.
Final reviewed source SHA256:
`46c5020dd05d9a5e547d0cf498d4aa3b34037cd40827ce52598620da6a6b883e`.
No semantic, owner, order, finish-frame, or busy-branch defect was found.

`body_finite` derives the current field load from original edge residency and
the current annotation heap. It calls the actual current ParentEdge.finite
with the owner's inherited value and original children. The independent
result EdgeLaw follows from the parent raw-edge language receipt and the
original edge interpretation. A result-language law is not a body input.
The returned caller has exactly the same outer edgeResults and nodeResults.
The checked native tables, merge cache, fourth memo, heap, and equality
operations are the literal returned current components, not reset states.

`evaluated` uses beginEdge_evaluate_sound to obtain the actual captured
owner, its inherited readiness, resident input, exact key, and evaluating
cell. Evaluating-phase Sound has no returned-result law. body_finite leaves
the entire outer edge table unchanged. Thus the same owner's cell remains
evaluating at the same handle. The actual derived result law is installed
only at finish. Key transport uses common-heap resident edge identity and
recorded inherited identity facts to transfer the owner's law to the later
candidate request. It does not assume owner and candidate are literally equal.

`ready_hit` obtains a returned owner's result and law from legitimate initial
warm Sound. It proves whole caller-state equality. It has no range-plan or
body-execution premise. The old law for an already returned cell is an
explicit initial warm invariant; no law for a new result is assumed.

`fresh` derives publication and evaluation from an actual missing key. It
does not assume successful body completion. `CallRanges` applies only to
actual evaluated owner states; `Ranges` sees actual loads and conditional
ParentEdge ranges. Reached machine word/range obligations remain explicit.
They are not semantic answer or future result-law assumptions.

`finite_or_busy` leaves an actual busy observation as the left alternative.
Structural linked Valid excludes absent observations. It does not exclude
busy states, establish outer recursive completion, or claim runtime progress.
This module completes the local reduced-edge result-cache body component.
It does not run the later inherited-descendant recursion or the full ordinary
node row traversal.

The first canonical log contained a new private unused-section-variable warning.
Root added explicit omit binders to not_absent. Public statements and proof
behavior did not change. The final hash above includes that correction.
Only root edited the source. The independent direct probe makes no Lake changes.

Validation command:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-inherited/partial-edge-call-independent-public.lean
```

Final terminal 0, no warnings/errors/sorry (`partial-edge-call-independent-public-3.log`).
Five public endpoint axiom checks and eight full API signatures pass.
Two independent derived theorem axiom checks and signatures also pass.
Six external integration examples, the actual evaluated-repeat theorem,
and the actual caller table-retention helper are kernel checked. The only
foundations are propext, Classical.choice, and Quot.sound.

The repeat theorem derives the old published request key from the actual
EdgeCall graph and the returned original-owner cell from evaluated. It then
calls beginEdge_ready and ready_hit at that literal returned state. It
derives a second actual call with unchanged whole state and global bundle.
It assumes no desired warm cell or lookup answer. The busy example derives
its own vacuous CallRanges and excludes the completed-call alternative with
the actual not_busy theorem. The cold example derives empty caller Sound
and missing-key facts from literal initialization. Other kernels check owner
alias laws, range-free warm reuse, fresh completion, and node/merge/fourth
frame retention.

Probe SHA256: `4afd5500f377c20f4ca4cf9d3d86ebc6961de51c0e85a63931f62332cfcf146a`.
Final log SHA256: `6590b1cbed9c7f1b7e4843b6d5c032ad0f24078b001ef68871502afa5f2d8aa7`.

Remaining source bridges: GHC lazy publication and winner reread, concurrent
memo effects, runtime black-hole behavior, native key/map correspondence,
machine identity capacity, and outer recursive termination. No new source
or proof module was changed during this independent review.
