# Current direct-parent union-find correspondence

Published base: 91fb8a9e751a0caa9df969b870a9c1ada5b3ecb9.
Imported main: c168a952d779a72294c34d9c8fd5afd0e308c5ab.
Direct-parent invariant: 9dfc776e8d8af30b3dcbf4229f46a374275ad476.
Exact-root and equality correspondence: 75c3a79613f36597c57c22889e3680f6a8adc90e.
The full goal stays ACTIVE and incomplete. Keep the optimized interned core as
primary. Preserve all older proofs, counterexamples, repairs and marked drafts.
The preceding checkpoint is notes-current-pruning-native-rendering.md.

## Strongest current statements

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
system language theorem. Covered closed construction, valid constraint allocation
and formal guard/entailment semantics supply a finite modeled processing trace
for any chosen budget and number of rounds. Derived mathematical width and fuels
suffice. With the empty inherited payload, the final available node accepts
exactly the original finite trees in every ambient environment. H6 is unchanged.
Its source SHA256 is e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5.

The preceding captured rendering theorem remains unchanged. Under actual stable
captured completion, the stated admission and semantic gates, structural discharge,
a successful native render and checks of its actual residuals, the rendered term
belongs to the original edge and parent. That proof constructs its satisfying
assignment and derives final Safe and dependency order. It does not derive
completion, discharge or rendering existence for the whole recursive scheduler.

The new local statement concerns the current union-find representation. Starting
with singleton initialization, any finite ordered union history preserves direct
parents, complete finite class membership and exact class cardinalities. The
allowed value assignments are precisely the conjunction of the requested pair
equalities. Repeated requests and variables absent from initialization are covered.
Each current operation has a corresponding actual finite earlier execution.
Their representative names and stored sizes agree at every variable. Their
map contents and parent paths can differ.

## Current source model and invariant

FlatUnionFind.lean models Nat identifiers and a functional persistent map.
A root has a size and a finite member list. Lists describe set membership only.
The list order is not the IntSet iteration or union order. A missing entry has
the singleton default. Duplicate initialization inputs do not change the map.
root reads one parent pointer. find returns the same forest.

Valid.parents requires each parent target to have a stored root record. This
excludes chains, cycles and dangling parent targets. Valid.roots requires Nodup,
size equal to list length, and membership iff the direct root equals that root.
entryOf_spec derives exact metadata for absent singleton roots too. No extra
absent-root premise is assumed. A weaker root-record-only condition permits a
stale parent after union and does not suffice.

redirectMembers_lookup proves the exact fold effect even for duplicate lists.
The complete merge redirects the losing members and then writes the winning
root. The full metadata invariant need not hold during that fold. link_root
proves its precise representative-redirection equation. link_valid proves the
complete final invariant and disjointness of the two appended member lists.
unionRoots compares stored sizes and selects the first root on a tie. Its theorem
requires distinct actual representatives, as the source API documentation does.
union resolves both roots, handles an already equal pair without a write, and
derives those preconditions for the distinct case.

## Exact-root correspondence

Represents flat earlier gives a finite earlier Reaches path for every Nat.
Its result is exactly root flat uv and the metadata size at that representative.
Path uniqueness therefore fixes every earlier path's root and size. A class-only
relation would lose the weighted winner and the identities of later value slots.

findRoot_represents identifies the actual completed earlier lookup result and
retains the relation at its returned forest. find_refines derives existence of
a finite earlier lookup. The current find retains its map, while the earlier
worker can compress paths or materialize a missing singleton root.

link_represents uses the old link_reaches theorem with the new root and size
equations. union_represents covers every successful earlier union observation.
It uses the actual first returned forest for the second lookup. Both exact
root names and sizes select the same union branch. union_refines derives a
successful finite earlier execution from Total; it does not assume future success.
compressed_union_represents also covers the earlier conditional-write worker.

EarlierUnions retains actual bounded calls in request order. unions_refine
constructs such a trace for every finite request list and retains final validity
and exact roots and sizes. Bounds are existential per call. No common fuel bound
or whole recursive scheduler correspondence is exported here.

union_classes, union_satisfies and unions_satisfies give the exact equality
semantics. initialized_unions_satisfies removes the initial assignment premise
because singleton initialization imposes no distinct-variable equality.

## Validation and retained attempts

All four final sources and the changed Audit pass warningAsError and linter.all
with Lean 4.34.1. Aggregate Audit passes 3982 jobs and checks 78124 theorem
dependencies. Only propext, Classical.choice and Quot.sound are permitted.
The unchanged old unused-input warning remains at
InternedFreshOrdinaryClosedCompletion.lean:24 in the aggregate build.

Installed public readback checks 28 new public theorems and unchanged H6.
It prints 18 complete definitions, including the operational workers, Valid,
Represents and the finite earlier trace. No placeholder or project axiom is added.
Every checked final source equals its installed and committed source.

A focused probe runs current Haskell inside the project Nix shell. It compares
8 states and 11 root reads per state with the Lean model: all 88 agree. Requests
include ties, absent singleton roots, a losing class with existing parents and
redundant union. Final root 2 has size 7 and members {0,1,2,3,8,9,10} in both.
Haskell find retains its entire forest for every tested variable and state.
Duplicate initialization and absent singleton reads pass. The two list orders
are different and intentionally compared as sets. This is a focused comparison,
not verified extraction or a general runtime correctness proof.

All jobs ran serially under a verified 4 GiB max/high cgroup cap with zero swap.
The repository instructions require these checks. No new runtime tests or
Haskell source edits were made. The existing full suite was not repeated.

Retain the failed strict drafts: missing documentation, constructor disjointness,
let reduction, monadic simplification and the initial metadata case split.
strict-flat-semantics-1 also passed before the finite-history assignment theorem
was added; strict-flat-semantics-2 is the final checked source.
The first axiom-list parser did not accept line wrapping; the corrected parser
strips whitespace around each comma-separated axiom. Two source-pin verifier
drafts did not propagate source paths correctly. Both drafts and their errors
remain. The final verifier checks 92 whole files and 89 literal inclusive spans
across six pin files, without stripping final newlines.

The three bounded source reviews report CLEAR. Each review pins the exact final
sources and passing strict snapshots. These reviews do not claim independent
compiler execution. Original drafts and all reports remain in the evidence.

## External Haskell repair

The current imported source still exhibits the verified constrained extract
failure. PR #182 is open and unmerged at
f961332e59eb5a06fa151a7cf3647232b6ebd05b, based on the imported main.
GitHub readback confirms its source changes: extract takes the first termsByCost
result, requires child-cost monotonicity, and documents nontermination for an
infinite language rejected by all constraints. It adds the constrained regression
and removes the property that became an identity. The author reports the repaired
native output and 341 passing examples. This checkout has not applied that open
PR or rerun its tests. FINDINGS retains the exact native baseline failure,
the external repair status and the cost-contract caveat.
PR: https://github.com/TharkunAB/cfta/pull/182.

The authorized msg-board workflow records both the defect and this progress in
thread 1c1333d7-46ea-4f46-a9a1-b5d13e577337. The latest post has request ID
c9ad6e97-4c08-4efa-9483-952afcb6cce1. The exact arguments and receipt are retained.

## Remaining work

1. Relate the complete enumeration state across the two forest representations.
   Keep counter, values, obligations, ancestry and native Caller endpoints exact.
   Transport representative, union, getValue, assimilation and callbacks through
   the relation. The existing CPS exact-result proofs describe the older backend.
2. Retain Canonical through the remaining recursive prefix and callback history.
   Derive numeric Ranges from genuine resource receipts where possible.
3. Connect actual recursive outputs to discharge and rendering existence. Cover
   partial stops, recursive truncation and selector behavior explicitly. Prove
   emitted-term soundness and forward completeness for the whole admitted worker.
4. Keep concrete IntMap/IntSet extraction, negative Int identifiers, overflow,
   practical resource bounds, guard solvers, full typing/pruning, EGraph and
   cost-ordered API semantics outside current system claims until proved.
5. Refresh main before new work. Evaluate and import the extract repair after
   it merges. Preserve all baseline evidence and earlier repairs.

Evidence: lean/restart-evidence/20261027-flat-union-find.
The snapshot has 165 payload files and one manifest, with 1027908 payload bytes.
The manifest SHA256 is
0fa7bf78971dbd3452db6a6867ca9f71afbac84f7b29b3fa54be18b49f57a2f8.
The manifest records every payload byte count and SHA256. Raw logs and four
literal source cuts use lossless gzip. Decoded hashes remain in their records.
The first staging check rejected the cuts' original final blank lines. The
original manifest, archive metadata and failed check remain in staging-attempt-1.
No source byte was stripped. Only proof-change.patch is excluded from the final
Git whitespace check.
