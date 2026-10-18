# Finite union source induction with a fixed observation reader

Reviewed at 2026-10-18T10:15:20.274307+00:00.
Production `lean/MicroCFTA/SourceCurrentReaderFiniteUnionStep.lean`.
SHA-256 `cfda0e0276e825deab15385eab899a955b575b3a9ecf8348a52e4d667a0ea005`.
Public head: `SourceCurrentReaderFiniteUnionStep.union`.
Dependency `SourceCurrentFiniteObservationExecution` is pinned at final
`a2707b38abffc944c93e656365855a9cb89a8e36600ece6780b56bea332b90ae`.

## Exact source step

The theorem uses `AlignedAt depth view common expression`. `view` is the
fixed observation reader. `common` is the actual execution heap. Paired
lexical inputs use `RelatedAt depth view`, regardless of the execution heap.

The member hypothesis is explicit and stronger than a same-reader clause.
It quantifies an exact source member index, its lookup equation, a strict
syntax-size witness, and every executionReader. It supplies only
`AlignedAt depth view executionReader child` for that strict member.
It does not supply the relation for the whole union or for a future selected
Mu record. Source members can contain arbitrary nested and used Mu syntax.
Their required member induction cases remain explicit obligations.

The proof inverts both actual warm union source calls. It derives the raw
member values, actual buildMany equations, initial availability, and literal
makeUnion equations. Initial Ready and Replacements construct both ordered
stored member schedules. These calls can allocate missing grouped ordinary
nodes. Keeps supplies the later execution Ready, availability, and histories.
Actual source calls and stored calls replay at that produced execution heap.
The same indexed member hypotheses then derive their finite result relation.

The lexical Paired relation is unchanged during these execution effects.
No RelatedAt or Same relation is transported along Grows. The proof instantiates
the existing uniform union fusion at the original `view`, not at the later
execution reader. It derives physical Empty agreement separately with actual
union survival. Ordered finite observations compose through the actual member
lists. Complete row guards and ordered children remain in Same.

## Source-built boundary and integration

The fixture constructs a source containing USED `mu x.(f[x] | g[x])` and a
closed leaf replacement. It derives initial Ready from the actual closed
source build. Available raw nodes, the local reference, and the replacement
come from that source heap. Actual stored reconstruction gives Keeps to a
later reader. The fixture proves the reader's node counter increases by one.

At that reader, the raw source union and its stored reconstruction are warm.
The original `f[x]` source member also builds warm. Its stored reconstruction
under the same leaf replacement allocates one new grouped node. The fixture
retains the literal calls and proves memberAfter.nodes.next=reader.nodes.next+1
and memberAfter!=reader. It therefore refutes the proposed warm-member closure
route. It does not refute the finite union relation theorem.

The same fixture invokes the new union theorem at depth 2 with observation
view=the earlier initial heap and execution common=the later reader. Its
strict member hypotheses are proved universally from the cross-execution
ordinary and variable clauses. Both compared maps and results are identical
in this fixture; no distinct-replacement claim is made. The exact surviving
rows are f/false and g/true, with the closed leaf as each ordered child.
There is one constructed pair and no auxiliary pair.

## Remaining boundary

The theorem does not infer that the original same-reader-only child IH is
sufficient. It requires the stated cross-execution IH. No BinderFree, noDeep,
finite Cap, whole-heap closure, parent output relation, or observation-reader
growth transport is assumed. General binder and chronological earlier-winner
alignment remain open. This is an induction step, not recursive completion.

## Selected checks

Strict `reader-union-direct-1`: exit 0; raw log exactly 0 bytes.
Canonical `reader-union-canonical-1`: exit 0; warning-free, 601 jobs.
Full imported public `reader-union-public-1`: one public pair.
Fixture `reader-union-kernels-3`: exit 0; raw log exactly 0 bytes.
Full fixture `reader-union-kernels-public-2`: one constructed pair.
Every public pair has all eight explicit linter/printing options, #check @,
full #print, and #print axioms. The output has no omission, printer failure,
warning, error, or sorryAx. Only the three standard axioms occur.

All selected workers record effective memory.max=4294967296,
memory.high=4294967296, and memory.swap.max=0. The runner uses pinned Lean
4.34.1 with a five-minute timeout and an owned peak file.
Fixture-1 failed on a qualified reference_available name and list membership
simplification. Fixture-2 passed. Fixture-3 adds the explicit changed-reader
counter and both full surviving-row fields. Earlier snapshots and full logs
remain unchanged. No old source/evidence or mutable root artifact is modified
or included in the manifest allowlist.
