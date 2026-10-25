# Allocated pending IDs from concrete callbacks

## Current result

Rendering and match bounds: `3c1d159ff`.
Concrete callback output: `f6f7985dc`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The concrete Left callback now returns only allocated pending IDs in its
actual metadata result. The stronger finite producer uses the same fuel,
result and final cache as the earlier completion theorem. It does not rerun
the callback or require a desired final state. The earlier callback producer
types stay exact. The output-bound gap from the preceding checkpoint is closed.

## Preservation chain

EnumerationPartialBounds.TermBound checks every hole label in a partial term.
TermsBound applies that requirement to its finite ordered child list.
expandPartial_bounded proves both RenderStable and the bound at the actual
returned allocation counter. It uses actual bounded getValue reads and
storage bounds for expanded fragments. Pending holes retain their raw IDs.
The recursive empty-bucket case retains the existing truncation behavior.
This successful-execution theorem does not require Stratified or a completed
graph. The separate finite producer still requires dependency levels.

SourcePruningPartialMatch.PendingBound checks each parked entry's raw ID.
matchPartial_bounded proves that successful matching can only park holes
already present in the bounded partial term. It covers all pattern forms,
both wildcards, exact and prefix child matching, holes and truncation.
The private child matcher concatenates the bounded results in order.

programs_bounded retains bounds for the exact app and filter program views.
startMatches_bounded applies matching at those selected programs.
finishChecks_bounded retains bounds through optional-result filtering and
the final nonempty-group filter. No group order or duplicate is changed.

resume_bounded uses the actual representative-read path for each parked ID.
An allocated input has an allocated representative. If that root is current,
matching uses the bounded rendered term. Otherwise the exact representative
is parked again. The proof sequences all optional results and concatenates
their pieces. It retains the actual final allocation counter through every
compression step. Safety follows from bounded reads, never Frame alone.

oracle_inl_bounded covers early rejection, idle and full observation.
The observation reads every pending group before combining results.
Its output groups come from bounded resumption or bounded startMatches.
The bound holds for either rejection flag. No acceptance premise is used.

recordTypes_inl_bounded handles the empty-catalog branch and actual oracle
branch. recordTypes_inl_complete_bounded applies this result to the exact
earlier completion witness. It returns safe storage, full Frame, unchanged
dependency levels, the exact type-position update, unchanged openHoles and
typing, and allocated IDs for all returned metadata.pending groups.

## Verification and evidence

All six changed modules pass Lean 4.34.1 with all linters and warnings as
errors. Twelve strict attempts contain six retained failures. Renderer
substitution accounts for one. Matcher recursor binders and singleton
substitution account for two; unused simplifier arguments account for one.
Resume state substitutions and an unused section instance account for one;
the strict linter rejects the first omit-based repair in another. The final
proof puts the pure helper outside that instance section. All six final
strict checks pass. Template, oracle and callback checks pass first time.

Four installed helper builds pass. Aggregate Audit passes with 3761 jobs
and 76809 checked dependencies. Audit source stays byte-identical.
Installed public readback checks ten new preservation theorems, both older
callback producers and H6. Its full output has 230 lines
and 17191 bytes. Its SHA-256 is
`55e1147d69d6e4286b9db3cf852f3833b5e2a42f64d751806741607455a80423`.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The old unused inputs warning remains unchanged. All eighteen checks run
serially under 4 GiB heavy-management caps with no swap.

Source review confirms actual endpoint bounds, both rejection outcomes,
all new and resumed groups, and reuse of the same completion witness.
Preservation checks retain all previous runtime expressions and theorem
text. New predicates and appended proofs account for the changes.
H6, native workers and every Haskell source stay unchanged. No Haskell
suite is repeated. No new Haskell defect or repair is identified.
Root FINDINGS keeps the external Haskell handoff first.
Full attempted sources, logs, reports, final snapshots, proof patch,
cap records and preservation checks remain in
restart-evidence/20261025-callback-bounds.

## Remaining work and strongest claim

Initial metadata still needs genuine allocated pending IDs. The theorem
now preserves that property at its output. Other native operations must
transport it to later caches when the allocation counter grows.
The new theorem does not bound every metadata field or establish native
Int, IntSet or physical container correspondence.

Establish and preserve Stratified through native traversal, pending-class
merges and final fragment writes. Reuse the existing graph worker's
traversal_stratified and write_stratified design. Derive that each returned
fragment hole resolves to a pending slot at the actual traversal endpoint.
PendingReferences alone does not prove fragment acyclicity.

Connect the supplied Graph.node classification to the actual native heap
and handle decoding. Compose each Left callback at its own successful
branch receipt's Caller, memos, queries, cache and metadata. Retain source
callback/recursive-loop timing and rejection. Arbitrary Haskell forcing,
scheduler restart, initial-only capacity forecasts, extraction and whole-driver
language semantics remain open. No whole-loop termination is proved.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache, original allocation history and any
prescribed finite budget and modeled node-call rounds derive sufficient
finite bounds and one mathematical width chosen after construction. With
empty inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.
Concrete solver and physical runtime correspondence remain outside that claim.
