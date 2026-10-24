# Concrete template oracle source review

Reviewed at 2026-10-24 03:15:24 CEST. Status: CLEAR. No callback sequencing, result-combination, full-symbol, frame, finite-transport or common-bound error was found. I read all320 lines of the original frozen callback, its complete self-review, relevant native branches and complete V1-to-V2 repair diff. I authored the pure helper module and earlier observer foundations, but not Required's callback source or Root's callback repair. This is independent review of the callback and its use of those APIs, not independent reproof of my authored foundations. No compiler, prepared program or repository write was performed for this review.

The frozen V1 source has20843bytes and SHA256 `fc4a5749a8754f02f7d5f953e8fe888a2cff874e296cc3c1450df37d45416b49`. The selected V2 retains320lines,20956bytes and SHA256 `cb782c5dcc18b8dfe87927778523df97f38c9cf3fe1e9946e4f24f1ffbdc69e0`. All9 owner payload files, byte/hash pins and complete owner file set were checked. The original frozen owner remains unchanged.

The model follows the actual Pruning.hs219–250 branch order:

- A pre-expansion Right event returns `(false, pending)` without a state read. Its ignored node is the existing graph-ID representation; no native node-representation theorem is claimed. Public `oracle_inr` states the exact action equation.
- For a Left fragment, pure early rejection comes before the empty-pending concrete-root shortcut. Rejection returns `(true, pending)`, retaining the entire original pending list.
- The idle shortcut requires an empty OUTER pending list and a concrete node outside exact ordinary app/4 and filter/2. A hole never takes that shortcut. A pending list containing an empty group is not an empty outer list and still enters observation.
- The remaining branch executes exactly one existing `expandPartial`, then traverses every pending group in order with the existing resume at the same raw current ID and rendered term. Only after all stateful group reads does it apply pure finishChecks to resumed results followed by started matches. There is no second render or substituted intermediate state.

The Option semantics are exact. `none` means that a particular match failed and is omitted by catMaybes; it does not itself prune. `some []` proves a completed match and sets the prune flag. Every nonempty completed check remains in source order, with duplicates, even when another check sets prune=true. Neither result skips later stateful group reads. The pure helper's exact tagged index and program order are used directly; no arbitrary matcher or candidate selector was introduced.

The alphabet is the existing complete `SourceObservations.Label FullSyntax.Formula`, including refinements. Graph, template, partial term, pending pieces and outputs all use that same type. Existing executable formula equality is selected locally. Recognition uses full ordinary Top app/filter/arrow labels, not name-only comparisons. Native Symbol interning, Text, Formula and map representation refinements remain explicit boundaries. This review also accepts the documented citation-only helper-review erratum: fragmentTerm is at native Pruning.hs348–350, not347–352; the frozen helper code and actual source-index enclosing cut were correct.

The proofs use the actual intermediate states:

`groups_agree` splits both actual ordered head reads and tails, compares their head results with resume_agrees, and recurses from those actual middle states. Left middle totality comes from the actual head's preserved frame. It preserves the complete ordered result list and final Frame. `groups_transport` constructs each right head and right tail from one observed left traversal. It uses firstFuel+restFuel and existing exact-state successful fuel extension, so neither middle nor final state is guessed or replaced. The empty traversal constructs a real pure success at fuel0.

`observe_frame` composes the actual render frame, an ordered mapM invariant for every resume group, and the last pure action. `observe_agrees` first obtains the same rendered partial term from two actual successes at independent fuels. It then compares resumed lists from the actual render endpoints and applies the same pure start/finish computations. There is no read-only-state or arbitrary-output-congruence assumption.

`observe_transport` constructs a right render at renderFuel, giving the actual rightMiddle. It then constructs right group traversal at groupFuel from that exact rightMiddle. The final common right bound is renderFuel+groupFuel. expandPartial_moreFuel raises the render while retaining rightMiddle; resume_moreFuel raises every group traversal while retaining rightLast. Nat.add_comm aligns the two sums. The final pure result is the actual same finishChecks result. The theorem constructs the right success and its frame from one actual left success; it has no desired right-success or final-frame premise.

The public oracle_frame, oracle_agrees, oracle_moreFuel and oracle_transport split only the actual pure/observing source branches. Their only forest premise is left totality where used. The raw current, graph, template catalog, pending list and input event are shared. Paired agreement permits independent successful fuels. Transport chooses a finite right fuel; pure branches construct0. Successful fuel extension retains the exact optional result and full final state. It does not assert equality of error lists, complete result streams, branch multiplicity, physical forests or same-bound execution across different forests. No Safe, Finished, accepted-completion, canonical-current, desired-output or pruning-soundness premise was added.

The Frame is the existing complete relation: counter, values, obligations, both ancestry fields and exact root-ID/size reachability in both directions. The source has no new axiom, sorry/admit, unsafe action, proof-limit override or alternate observer. This result does not establish unconditional rendering termination, general term-order correctness, template pruning soundness, full cached-driver congruence, native implementation refinement, resources or convergence.

Root's exact repair is narrow. One private existential binder changes from rightFuel to _rightFuel. All uses of deprecated if_pos/if_neg change to ite_eq_left/ite_eq_right. Installed Init/Core.lean1179–1194 shows that these are the exact replacement theorems for the same positive/negative conditional equations. A direct text transformation reproduces V2 exactly; all5 public theorem statements and every executable definition/context byte remain unchanged. The original first strict attempt is retained as exit1: its3095-byte log contains only the unused-binder diagnostic and20 deprecated-alias diagnostics. It contains no unresolved proof goal. The successful V2 strict report has exit0, literal-empty output, warningAsError and all linters. Its checked input and installed module both equal the V2 hash above. Root's pure-helper repair similarly changes only fragmentTerm_hole's proof from rfl to simp only [fragmentTerm], with no helper executable or interface change.

Exact inspected input hashes:

| Input | SHA256 |
| --- | --- |
| Frozen owner self-review.md | `89c24fdede110df0f535199eca938f78050f27af4a47d9ec376672f0536ffa4a` |
| Frozen owner source-index.json | `de3115bea16fcf9982068e3ede5104c7fd07572c417ca0fb29336e5bfbdbb8d4` |
| Frozen owner pins.json | `ee12281f1c9896d2251862820ce609312ece21b0cc0d859e66fc87adbea87a88` |
| Frozen owner FROZEN.json | `2899841bb6fccab8b953c3473d2190c92fdf1feb0a92f7ea327187a79ae86a3c` |
| Original oracle-check-1/report.json | `08ada29b21ee490f151a4b9041a6242c7c8f968afc3afb6508e24ad3c546c129` |
| Original oracle-check-1/raw.log | `a44350ebbf30d3220b38cb3bd4e5322f634be053afc0c85be5ea75792663f13a` |
| Selected oracle-check-2/report.json | `79d04c0c2ec10abf02406b6e9a918a6786dd06f5b6070a8dbda6155703aace59` |
| Root oracle-v2.patch | `b8810014602f8d447b84a07d8d0a3844a882fafee86434719a9585ce51068674` |
| Selected helper SourcePruningTemplates-v2.lean | `1890878e308ec4debe67d6e74755bc00d93898f59a3a4ed1e5fa188c02899156` |
| Live Pruning.hs | `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` |

This is a completed source/repair review. Aggregate Audit and public readback are separate actual validation records and are not inferred here from source review or Root's pending run.
