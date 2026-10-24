# Template oracle public declaration review

Reviewed at 2026-10-24 03:17:16 CEST. Status: **PUBLIC_DECLARATIONS_CLEAR**. No correction is required.

I manually read every line of the complete public readback, lines 1–155, in two untruncated cuts. This includes all 27 declaration signatures in the recorded order and all 13 axiom reports. I also read the exact printer input, declaration inventory, installed helper definitions and public theorem statements, and the installed oracle definition and public theorem statements. This report does not claim a second manual whole-body review of the 320-line oracle. I did not author either new module, run Lean or Lake, or edit repository files.

The 27 signatures are exactly the 21 helper declarations plus the oracle and its five public theorems. The printer input has exactly these 27 `#check` commands and exactly the 13 recorded theorem axiom commands. Its bytes equal the checked printer snapshot. Read-only checks verified the public receipt source hash, complete raw-output hash and byte count, declaration order, unique names, and exact axiom-report coverage. No public type contains a private helper, `_private`, `._@`, `✝`, or `sorryAx`. No new axiom, opaque or unsafe declaration occurs in the two new source files.

`Symbol` remains the existing full `SourceObservations.Label FullSyntax.Formula`. It includes both the name and the refinement. The public application and filter equations use literal `.top` refinements. The known-head theorem exposes the actual original-position tagged generic/fixed lookup union and ascending `List.range` selection. The unknown-head theorem returns the original catalog. These statements preserve duplicate catalog entries at different positions. The raw fragment-hole equation retains its raw ID. The nil equations concern empty results and candidates only.

The oracle takes one fixed graph, catalog, pending list, raw current ID and input. `oracle_inr` is equality with `pure (false, pending)`. `oracle_frame` requires representative totality and one actual successful callback and returns the full compression frame. `oracle_agrees` allows independent left and right fuel and actual successful callbacks from framed inputs, then proves complete result equality and a full final-state frame. It does not require equal fuel. `oracle_moreFuel` retains the identical result and complete final state. `oracle_transport` takes a frame, left totality and one successful left callback, then constructs an independently finite right fuel and actual right final state with the same complete result and final frame. It has no right-success, desired-output, canonical-current, Safe, Finished or pruning-soundness premise.

Actual axiom dependencies are as follows. They are not all axiom-free or limited to `propext` and `Quot.sound`.

| Theorem names | Actual axioms |
| --- | --- |
| `finishChecks_nil`, `order_nil` | none |
| `fragmentTerm_hole` | `propext`, `Quot.sound` |
| `indexTemplates_unknown`, `indexTemplates_known`, `programs_filter`, `programs_app`, `rejectEarly_hole`, `oracle_inr`, `oracle_frame`, `oracle_agrees`, `oracle_moreFuel`, `oracle_transport` | `propext`, `Classical.choice`, `Quot.sound` |

The full-formula helper code uses the existing executable formula equality and its proved dependencies. `Classical.choice` is a standard permitted dependency in the current Audit allowlist, alongside `propext` and `Quot.sound`. The actual reports contain no project-specific axiom. Both installed sources equal the corresponding final V2 files. Their final strict receipts report exit 0 with empty logs under warning-as-error and all linters. Root's aggregate Audit receipt and raw output agree: 3,675 jobs and 75,838 checked theorem dependencies; one replayed older unused-`inputs` warning remains in `InternedFreshOrdinaryClosedCompletion`.

This is an observation and source-model scope review. It does not prove the semantic validity of early template erasure, pruning soundness or completeness, native container or interning extraction, native integer bounds, arbitrary callback congruence, unconditional termination, or the full enumeration driver. It does not enlarge the previous source review or replace Root's publication gates.

## Checked input identities

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| `/tmp/mcfta-template-oracle-20261024/public-1/raw.log` | 12082 | `5347594be81c1632947c62bf7ba0738cdc8015074f25cc1faf16d18b45aef128` |
| `/tmp/mcfta-template-oracle-20261024/public-declarations.json` | 2193 | `3a99e63b3cf900a39d945b23389668b5c61694f9a77b3b927a3abc8006fd26e8` |
| `/tmp/mcfta-template-oracle-20261024/public-1/checked.lean` | 2303 | `6c97a8700513ca69e0af69d2190e94286dedefd7084dd33468142aebf76d7ccc` |
| `/tmp/mcfta-template-oracle-20261024/public-1/report.json` | 488 | `ac9e8093dc888025c920bb005e69d17cf304f981262a376801a5e86fd2edc6b4` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningTemplates.lean` | 8380 | `1890878e308ec4debe67d6e74755bc00d93898f59a3a4ed1e5fa188c02899156` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningOracle.lean` | 20956 | `cb782c5dcc18b8dfe87927778523df97f38c9cf3fe1e9946e4f24f1ffbdc69e0` |
| `/tmp/mcfta-template-oracle-20261024/templates-check-2/report.json` | 502 | `967b1982529101ca46bc4a56a324945e2829ce520856344e9c0535e36d42e691` |
| `/tmp/mcfta-template-oracle-20261024/oracle-check-2/report.json` | 496 | `79d04c0c2ec10abf02406b6e9a918a6786dd06f5b6070a8dbda6155703aace59` |
| `/tmp/mcfta-template-oracle-20261024/audit-1/raw.log` | 676 | `fc0c6e41bda63beb93c2d19556f0db434acaf04586137881b2d9eb434e215a42` |
| `/tmp/mcfta-template-oracle-20261024/audit-1/report.json` | 300 | `00329cf8cbf19d4f5ea85262045d25b6815474ff3bd2698124cb135d92ae61c8` |
