# Next producer after the checked assimilation fold

Measured metadata time: 2026-10-24T21:27:03+02:00

Recommend one concrete terminal-prefix producer that derives the original recorded roots and actual winner before the checked assimilation fold. It should construct the existing representative/union actions, preserve the complete recorded order and duplicates, and derive the fold's input-slot domain. This closes the caller-origin gap rather than adding another wrapper around a supplied successful fold.

The native order is explicit: record every old representative; union the first ORIGINAL suspended variable with each remaining ORIGINAL variable; resolve the winner; move distinct old waiting buckets except the winner; assimilate the ORIGINAL recorded list; finally merge the incoming node and descendant constraints. Do not union the recorded-root list or deduplicate the assimilation list. `SourceUnionFindCompression.find_eq/union_eq` already connect conditional-write source primitives to the modeled operations.

The necessary foundations exist. `EnumerationExecution.mapM_terminates`, `forM_terminates`, `representative_terminates` and `unionVariables_terminates` construct finite actions from totality. `EnumerationSchedule.representatives_scan`, `terminal_unions` and `merging_representative` describe their exact outputs. Those latter statements consume observed successes; they do not construct them. More importantly, `EnumerationCompleteness.mergeTerminal_terminates` already builds this prefix internally at176–215 and joins its three bounds at231–240. Its exported theorem also assumes old Graph intersection correctness and a satisfying assignment, then runs old assimilation. It cannot substitute for the current checked fold.

Use the existing local domain: initial `Safe`, allocated suspended references and `InputsPending`. `inputs_pendingAt` already derives a genuine pending value at each old representative. `pending_inputs` derives the avoidance premise from an actual stored pending payload plus `PendingReferences`. The prefix leaves values unchanged. Thus the computed recorded roots stay pending at its endpoint. The actual winner belongs to the selected old roots, so its target slot is pending too. `PendingRealized` transfers directly through unchanged values and unchanged native heap. Caller, operation cache and global memos stay identical throughout this prefix. No scan, union, winner or fold-success premise is needed in the new producer.

Include the completed waiting transfer from genuine initial canonical counts. Compute the distinct nonwinner keys from the recorded list; derive their membership rather than accept a keys/output law. `merging_roots`, `redirect_fold_eq` and `moveMany_correct` already connect that transfer to the SAME actual final forest. `recorded_transfer_correct` is useful conditional prior art, not an existence theorem. A count-only conclusion can avoid introducing a replacement Graph for candidate predicates. Host IntSet ordering/storage correspondence stays explicit.

Do not assert `Safe` or `LiveRoots` at the union-only endpoint: losing old roots still hold pending values until assimilation eliminates them. Do not assert a compression Frame across unions, which change classes and sizes. Exact nonforest fields and the actual merged-root map are the appropriate prefix conclusions.

A literal prefix action plus one finite producer appears manageable in roughly160–240 lines. Compose with Fold later at this computed endpoint under its explicit range admission; no duplicate query/worker receipt is needed. Remaining gaps include deriving caller safety/avoidance through the new native stages, initial-only width admission, the native root flag, cached candidate maintenance and host IDs. Incoming-node merge is also separate: native code writes and inherits ancestry BEFORE its final Empty guard, unlike assimilation's reject-before-write order. Full terminal/driver language preservation remains open. No prospective declaration or proof body is authored here.

The Fold row below pins its accepted V3 public contract only. Current Root proof attempts are not assigned a success verdict by this assessment.

| Source | Bytes | Whole SHA-256 | Exact cuts |
|---|---:|---|---|
| `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs` | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 489–525, 716–747 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationExecution.lean` | 30176 | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` | 371–428 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationSchedule.lean` | 86287 | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` | 36–75, 476–547, 550–578, 728–740 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCompleteness.lean` | 23285 | `1cafd52affc702de54e22a37e4ac12496d860b964c0628d95eb94f015fbf34f7` | 117–132, 168–215, 231–244 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationDependencies.lean` | 29230 | `d0ab8f9bf345495711bc2e98fe22e188f2d0f00229f13ea2e3c4de895f294a21` | 392–395 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationReferences.lean` | 39454 | `8c6f8fa2b6ffeb550da4b3b25bff7d5596910107d663c28987137231d61ba1fc` | 344–352 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCanonicalUnion.lean` | 9776 | `b76617ea7f0fb0ba74b78125f9c2232302e7513d378ddbfa8deef0fea9cf8bd6` | 20–65, 69–84, 127–155 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCanonicalWaiting.lean` | 14833 | `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd` | 35–60, 230–241, 244–274 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceUnionFindCompression.lean` | 7887 | `1a6d2adbf6c2886ffff91935f59b7cf9d68b32fc90593e3461af823af56b38e0` | 133–153 |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` | 20–26 |
| `/tmp/mcfta-pruning-enumeration-fold-20261024-proposal-v3/complete-header.lean.txt` | 3392 | `1514cc57ad0ed04b3f0616cb65300598f73632922adc18a89ba38a75144a90c4` | 1–47 |

All whole snapshots and line-exact LF cuts are retained in `/tmp/mcfta-pruning-enumeration-fold-20261024-next-assessment-inputs`. Every cut byte count/SHA-256 is in `source-index.json` (SHA-256 `8796df63be1ca92d0f2d4766b1a6b7e2a466d13f1de60b3356e74afa45bfee9b`).
