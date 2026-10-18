# Actual outer prefix invariants

Reviewed on 2026-10-18. The final source is
`SourceCurrentOuterPrefixInvariants.lean`, SHA256
`138c3f0e8cdff1aec2b94349bbd73ccb8f3b76308acd04bf18c1b698dbecbb43`.

## Result

Successful mutual outer calls derive their returned physical invariants.
Literal finite prefixes derive each reached state's invariants and operand
readiness from their entry facts. An actual outer node-busy failure derives
its own prefix and the invariant at its exact busy reader.

The initial `Good` contains `NativeOperationHeap.Good`, merge `Stored`,
physical filtered Mu probes, and weak physical outer result cells. Every
outer cell retains its exact key link, a ready inherited payload, and an
available node or resident edge input. Returned cells have available nodes
or resident edges. These cell facts assert no result language law.

Filtered probes are an explicit initial physical invariant. Actual source
construction derives it. It does not follow from the older `SemanticReady`
predicate alone. The new Native/Lower/Parent probe producers retain it
through actual completed calls. The outer proof does not assume it at
each prefix. It imposes no finite Cap, whole-forest closure, global plain
region, `NoDeep`, reached range, or reached-input plan.

## Actual successful calls

The private strong induction follows the literal outer fuel and all eight
worker families. Node and edge hits use their actual captured cells.
Evaluation checks the captured request at the post-demand state. A finish
stores the actual available or resident result at the selected handle.
It does not use a relation between a warm result and the later candidate.

The Parent case calls `SourceCurrentParentProbeHeap.parent` on its actual
successful Parent equation. Resident input rows supply their own allocated
fields and available children. Initial request readiness supplies the
inherited payload. The returned enhanced invariant supplies physical
filters. The final source contains no `ParentFilters` parameter or other
future callback preservation premise.

The Mu case calls `SourceCurrentMuReconstructionEffects.node_body`. Its
initial available resident Mu and filtered probes derive exact cleanup at
the unchanged full caller. Empty and explicit union bodies return as the
literal worker specifies. A raw reference has no successful body branch.
Ordinary rows and indexed child walks pass their actual returned states
to the next call. Raw reconstruction retains fields and physical payloads.

The inherited prefix derives a valid operation cache and a ready combined
payload from the current resident row and inherited Ready value. Indexed
descent derives its own new Ready payload. These are actual operation
receipts. No reached Ready value is supplied independently.

## Busy dispatch and owners

`reached` verifies the existing literal `Step` and `Reached` witnesses.
Those witnesses retain successful earlier worker equations. `busy` does
not ask for a desired prefix. It constructs one from an actual literal
`.failed (.nodeMemo handle .busy)` equation, using the earlier checked
failure extractor. It then derives current `Good` and request readiness.

`initial_busy` starts both outer tables empty. It derives the exact busy
dispatch, every active owner's enclosing activation and operation growth,
and Ready operands for every current evaluating node cell. The derived
cache validity and physical request residency turn the colliding complete
key into equality of the full owner and candidate requests. Thus inherited
payloads and full stored values agree, rather than only their identifiers.
This equality does not exclude a collision.

These conclusions concern the outer node-memo busy fault. They do not
assert invariant preservation for arbitrary Parent failures, nested native
faults, binder pending states, or exhausted final states. Earlier successful
prefixes are sufficient for the proved busy case. Parent `.done`
preservation is not treated as all-failure preservation.

## Constructed validation

The one public integration constructs a small source tree and its actual
empty equality-field allocation history. These facts derive initial native
Good, merge residency, physical filtered probes, and ready source operands.
It starts a leaf owner by the literal `beginNode` operation. It then runs
an ordinary root call through an actual Parent, descendants, and indexed
walk. The child call reports busy. The proof invokes `busy` and derives
full operation memo validity at that reader. The root remains evaluating
at its own handle.

This is a supported warm-prefix example. The leaf owner predates the root
worker entry. It is not a node-busy execution from two empty outer tables,
an initial counterexample to general completion, or a divergence example.
No future trace, returned invariant, or worker result is a public fixture
premise. Literal evaluation proves its execution equation. The exact
checked private statement has a public alias for complete proof printing.

## Evidence

Selected production strict attempt 13 has zero log bytes. Its canonical
build succeeds with 1824 jobs. The only canonical warning comes from the
unchanged `InternedFreshOrdinaryClosedCompletion.lean`. Public attempt 1
checks 24 distinct declarations: 18 handwritten heads, one constructor,
and five projections. All have full signatures, full proof prints, and
axiom reports with all eight printer options. Only the standard three
axioms occur. The checker rejects truncation and printer failures.

Kernel strict attempt 3 has zero log bytes. Kernel-public attempt 1 has
one full signature, proof, and axiom pair. All runs read back effective
4 GiB MemoryMax and MemoryHigh and zero swap. Every execution used its
unique immutable source snapshot. Every failed attempt and raw log remains.

Early strict attempts check partial foundations. Attempts 2 and 4 through
9 retain parser, simplification, qualification, inference, and unused-simp
diagnostics. Attempts 10 and 11 checked an intermediate private induction
parameterized by Parent filter preservation. That temporary argument was
removed when the actual Parent probe producer became available. Attempt
12 failed a shadowed state variable. Attempt 13 checks the concrete final
producer. Kernel attempts 1 and 2 retain a missing noncomputable marker
and a missing explicit phase argument. They are not selected as successful
evidence. No proof premise was weakened to repair these failures.

## Remaining obligations

This component does not establish general outer completion. It does not
exclude equality with every active owner's physical key. It separately
does not bound the number of fresh recursive requests. Parent can return
new values, so physical cache growth and no-busy would not alone prove
termination. General semantic native memo correctness and Haskell
correspondence remain separate obligations.
