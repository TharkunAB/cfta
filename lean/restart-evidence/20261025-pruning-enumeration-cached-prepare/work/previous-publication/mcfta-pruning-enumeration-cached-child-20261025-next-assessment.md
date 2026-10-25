[2026-10-25 03:49 CET] FINAL source-only next assessment. Recommendation: complete the missing cached ShallowChild shapes before a whole-edge cached traversal.

CachedChild.prepareOrdinary supports only decoded ordinary nodes with a false terminal test. General edge children are not all ordinary. ShallowChild.prepareChild also supports nonterminal Mu and Union through allocation only. Their stored slot has empty scs, even when the incoming nonterminal bucket is nonempty. Their fresh native flag is false because recursiveBoundary is true and the ACTUAL stored bucket is empty. Their waiting map does not gain that bucket. Applying the ordinary full-scs write to these shapes would change the source operation.

The smallest useful next scope is one general native cached-allocation producer and one remaining-shape child producer. Reuse CachedChild.allocate. Derive classification from the actual lookup/constructor, not a supplied flag/output law. Cover absent-node allocation as well: its fresh flag is false. The all-slot invariant must include absent slots above the counter, so a false allocation cannot retain a stale true fresh flag. Reuse State.allocate_exact, allocation_storage, Writes allocation-realization and CanonicalWaiting.allocate_correct. Retain the same raw core, unchanged forest/Roots and waiting, all pending slots, storage, fresh read/counter/hole bounds and every flag. Do not invoke the older Graph cached classifier or add another count identity.

For actual available closed Mu/Union, available_readback and ShallowChild.prepareChild_complete derive the handle and action. Prove its same core raw singleton against allocation, with no full-scs write or second inheritance. Empty must keep actual raw[] before allocation, including when its bucket has a terminal constraint. Reference remains a model-unsupported case. The native unresolved-reference error is not equal to model None. Missing decode is also model partiality; genuine available/closed input should discharge it through existing readback. Preserve the existing ordinary theorem. A rough next proof estimate is 180–300 ordinary lines; Root should select the exact interface and cap after header review. No new header is proposed here.

Only after this coverage should a cached child-list worker compose actual occurrences in order. Existing runStaged_complete derives the completed-prefix endpoint and first unsupported position; runStaged_exact turns that derived Success into an exact singleton. These are already proved core APIs, not cached executions. A new cached worker must retain its actual reached cache at interruption. It must derive finite bounds from Roots and the concrete buckets, including repeated children, rather than assume successful callbacks or future states. A valid parent derives child availability, closedness and nonemptiness through the existing Ready route; it does not derive that all children are ordinary.

Whole-edge caching also needs own equality-class allocation: suspendMany_exact gives suspendedState, and existing suspension_storage/suspended_realized retain storage and pending slots. Cached correctness at those repeated absent-node allocations is still required. Cached.frame cannot justify changing value slots. Residual recording changes only obligations and occurs after every child completes; it must not run at an unsupported child endpoint.

Finally, OrdinaryBranches preserves selected list order and duplicate occurrences, starting EACH alternative at the same before state. Its empty arity-rejected rows, outer missing-project None and inner unsupported-child None stay distinct. Native shallow termsPruneUntil uses canonical selection, while raw runsInterned follows the eager driver. Neither public entry is already identified with a shallow raw-order cached worker. Actual canonical order/membership, required-cache readiness, native expandable flags, driver initialization, machine bounds and extraction remain separate obligations. H6 is unchanged and the whole goal stays active.

The current CachedChild assessment uses the actual 255-line V5 source and recorded strict5 pass. It does not claim any future component, callback, complete wrapper or pipeline completion. No compiler, parser, proof/action body, selected program, repository/Git change, network or board operation ran here.

Exact source inputs (inclusive cuts; whole SHA256):

| ID | Whole bytes | SHA256 | Cuts |
| --- | ---: | --- | --- |
| native | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 385–405, 716–733, 783–801 |
| cachedChild | 16154 | `e58ee8a8ed76116afb51e7276096a3ae3169239e228fda0948ecaf50136fa15d` | 10–48, 50–69, 99–118, 138–147 |
| child | 6479 | `8210b17170fce05b31515e5f9b332799601fcfbc728263df6e2f53b917baed7c` | 15–33, 36–65 |
| nativeIndex | 9830 | `13c8b37a63e950f4b26d2e9c927cc3108b50b3024b96b3be70a8a539f6f7f160` | 16–30 |
| boundary | 9592 | `278e40fc5846b6f8614e4bf1025b8c7711c03dbad7b298bcccc2f1442f47a636` | 89–92 |
| canonical | 14833 | `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd` | 82–98 |
| nodes | 3546 | `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4` | 16–21 |
| state | 33489 | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 569–591 |
| correctness | 76898 | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 412–435, 840–858 |
| edgePrefix | 5270 | `fd80b9c8ff6d9f3656837186a18f584e2a077b0b703489b9077a9f56e5bc56d1` | 15–32, 34–51, 53–72 |
| traversal | 15377 | `9a071434740188ae3b03c06b6ed0487d1d3856aaaac0a8b0d7ff4bca4c1271bc` | 18–51, 104–117, 179–191 |
| exact | 8945 | `687a5e58c4403076a22e249a981c3a733bc3d5d4f5c32acd4f15af70022c07ae` | 13–23, 83–94 |
| branches | 6368 | `c46228a592055ff1c5cc844106676a953e7a238017308a82979254ddf2e8a558` | 13–50 |
