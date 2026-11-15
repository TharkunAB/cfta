# Actual eager clear-history carrier audit

Date: 2026-11-15, Europe/Stockholm. Parent checkpoint: `57c7b321...`.
Status: READ-ONLY SOURCE AUDIT. No theorem or new Lean module is claimed.
Source hashes identify this snapshot. No compiler was run.

No inspected producer derives the complete clear history of an indexed output
of the literal shared `runEager` worker. The first missing producer is operational:
attach the exact causal branch and all contributing true-clear receipts to each
actual output occurrence. This result must be derived from the fixed run.
It cannot consume a supplied history, a model, or future callback resources.

The existing parts are useful but do not supply this producer:

| Existing source result | Actual information | Missing information |
| --- | --- | --- |
| `SharedScanOutputOrigins.scan_output_origin` and its identity eager specialization | Output index; producing row and local index; exact completed earlier scan; same captured cache and reached native endpoint | Recursive history inside the row and nested eager children |
| `CurrentInitialEagerRootScanOrigin.initial_runEager_prepared_root_scan_origin` | Literal initial worker/preparation/row provenance | Complete recursive branch and all removed buckets |
| `CurrentProgramEagerOutputs.accepted_initial_root_scan_origin` | Same accepted `firstOrderRaw` result, native build/root, initializer and actual root scan; conditional partial completion | A constructed assignment and complete history |
| `CurrentProgramEagerResources.accepted_initial_identity_emitted_history` | Actual initialized identity eager resources; every emitted cache has PendingReferences and Stratified | The name “history” does not denote removed bucket events |
| `SharedParkedRawBucketReceipt.parked_singleton_removed_bucket_receipt` | One actual true-clear receipt, full raw bucket, canonical target, write/restart and alias facts | Extraction and accumulation for every contributing clear |
| `SharedIncomingNode.singleton_bucket_history` | One actual incoming write retains the old bucket and incoming prefix | Recovery after later clear or recursion |
| Private `IdentityActualSourceOrigin` and `IdentityActualFrameLedger` | Genuine local source task transitions and immutable ancestor resource snapshots | Whole worker output occurrence and complete clear-event derivation |
| `SharedNativeBranchCompletion.FragmentHistory` | Counter growth, PendingFragment and Stratified | Removed obligations or source execution trace |
| `SharedSelectedContinuations.ChildTraversal.Trace` | Exact repeated ChildDispatch calls | Arbitrary/eager child visitor, full worker history, output occurrence |
| Nonshared recursive/prepared `OutputHistory` and `ResourceHistory` | Actual histories for their own older workers | Equality to the shared eager worker; general indexed eager history |
| Prepared nonshared `ResourceHistory.sound` | Backward meaning from its supplied ResourceHistory, final Satisfies, arity and discharge | A model producer or an actual shared eager history |

`runEager_output_control` proves metadata/done control only. Native outcome,
body and opaque event traces record their respective local operations. None of
those inspected interfaces supplies the missing complete eager clear history.

## Why the branch matters

`SharedBranching.scan` passes the SAME captured symbolic cache to each sibling.
It passes the reached native caller and query memo to the next sibling. A single
list that accumulates every earlier sibling's symbolic clears is incorrect.
Sibling caches can reuse raw IDs. Each emitted occurrence needs its own branch
history, while native heap preservation can retain growth from earlier siblings.

Complete and stopped scans both append earlier output lists. The carrier must
preserve these lists exactly, including repeated equal Output values. Membership
alone must not be used to identify occurrences or merge their causal branches.

## Semantic boundary

`Recursion.clear_satisfies` states the exact same-assignment equivalence:
original Satisfies iff cleared Satisfies AND every removed Suspended.Holds.
The full goal needs ONE rho that satisfies the exact output cache, ALL removed
obligations on that output's branch, and the accepted original root completion.
Independent witnesses for separate clears cannot be combined without proof.
A structural pending-assignment extension does not by itself supply domains,
residual guards, original-root acceptance, or historically removed obligations.

The derived operational history is necessary for the inspected backward route.
It is not itself a finite-model proof. Compatibility of all historical Holds
with one finite assignment remains a separate obligation after extraction.
No reachable Haskell defect or source counterexample is established here.

## Scope and evidence

The inventory records all 13 source files with a literal `runEager` reference,
177 files whose names contain History, Trace or Retain, the generic child-worker
reference search over that set, and shared History/Trace declarations. We also
inspected the actual root/scan origin modules and local native/opaque traces.
These searches support the reported missing interface; they are not a proof
that no alternative implementation could exist under a different interface.

`EXACT-HEADERS.txt` preserves 28 exact source headers or small runtime bodies.
`header-map.json` provides their original file/line ranges and fragment hashes.
`header-context-map.json` preserves the preceding imports, namespace, notation,
variables and local attributes for the first 25 extracts as exact source lines.
The final three carrier type headers use their pinned original modules for context. Header extracts are not
standalone Lean modules.
`source-pins.json` pins every selected source and the older target document.
`PRESERVED-RELATION-TARGET.md` is a byte copy of the earlier complete causal
relation/joint-witness specification. Its older progress claims remain historical;
this audit does not reopen later completed generated-Type work.

No original full target, worker runtime, Haskell file, immutable old packet,
Git state, board entry or temporary directory was changed.
