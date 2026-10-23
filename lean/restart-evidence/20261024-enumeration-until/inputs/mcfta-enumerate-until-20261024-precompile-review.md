# Enumeration-until static precompile review

Reviewed at 2026-10-24 01:07 CEST. Status: **SOURCE CLEAR after the projection correction described below**. This is a static source review. It does not claim successful elaboration, kernel acceptance, or termination checking. The reviewer ran no compiler, Lean command, prepared program, network operation, or repository mutation. Root authored the projection and definition lemmas. Guard authored the operational definitions. The reviewer authored none of these candidates.

## Reviewed inputs

| Input | SHA256 |
| --- | --- |
| Corrected projection, `/tmp/mcfta-enumerate-until-20261024-projection.lean`, 71 lines | `e216854d8d2fb0e07bb927c017af8be0a29188576d8f7d5ed54cd505e223b5f6` |
| Definitions, `/tmp/mcfta-enumerate-until-20261024-definitions.lean`, 154 lines | `db112904afe327470cc4b73b79976e055d6e5b4b973a57f567648ec7318f64cd` |
| Definition lemmas, `/tmp/mcfta-enumerate-until-20261024-definition-proofs.lean` | `99f102335cc31dedfb90b2dad6ac8d1d3654767b9acc62d0141330cec33b8b76` |
| Live `lean/MicroCFTA/EnumerationState.lean` | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` |
| Live `lean/MicroCFTA/EnumerationDriver.lean` | `0769d78e4d3c01d959cf21c5a59642fee164dc60655e86601458a799da72bbcf` |
| Live `lean/MicroCFTA/EnumerationCorrectness.lean` | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` |
| Live `lean/MicroCFTA/EnumerationCPSChecked.lean` | `ee4878e3a8da7ef380b971d8381e48e13f744b1a88c4c68c4b88fb95cb151d04` |
| Live `cfta/src/Data/CFTA/Enumeration.hs` | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` |

All candidate text above was read. The live `run_bind`, `Success`, `successes`, `mem_successes`, old eager worker/loop, shallow helpers, shared source loop, and partial renderer were checked against their actual definitions. Repository HEAD at this read was `790c39ce21f0be612fafcb6a36eb972ac5bf03f9`.

## Projection finding and correction

The initial 70-line projection had SHA256 `b369d816a605b8ffca2782844bce3321795289ca41b7d3a9262f45129f0d4fdc`. In `successes_bind_congr`, `induction rows` automatically generalized both `rowsEq` and `memberSame`. Thus the first argument of `ih` was an equality between the original success list and the tail. The proof supplied the tail membership predicate instead. This is a type mismatch, not a mathematical counterexample.

Root added `clear rowsEq` after deriving `memberSame` and before the induction. The current proof then generalizes only the membership hypothesis needed by the tail call. I reread the corrected proof. The `mem_successes` argument order and equality transport agree with the live helper. The projection preserves order and multiplicity of successful `(value, state)` rows. It deliberately discards errors. `successes_empty` uses the actual list membership equivalence. The local Monad/LawfulMonad definitions match the established checked enumeration module. No further definite static type or proof error was found.

## Definitions and fuel

The positive-bound stop test reads every candidate, including blocked slots, before scheduling. It requires a nonempty candidate list. Normal completion returns `none`; early stop returns `some oracleState`. With no stop rule the extra stop-state read is absent. Fuel zero reports `.fuelExhausted` before any stop test. This is the established bounded-model policy; Haskell has no corresponding explicit fuel error.

The selected-slot branch checks repeated recursion before narrowing. A repeated key clears the suspended list and recurses without either callback. Otherwise the narrowed empty view rejects before the pre-callback. Equal node IDs cause no extra write. A changed ID writes the original suspended list to the resolved slot. The pre-callback sees the narrowed ID. The worker then rereads the actual slot, so callback effects are retained. The post-callback receives the produced fragment and the pre-callback's caller state. Recursion receives the post-callback's caller state.

`enumerateOutWith` captures the representative after that reread, sets expansion ancestry from the selected stored node, unfolds a recursive body, clears expansion ancestry after expansion, and writes to the captured representative. It does not resolve a new destination after expansion. The same-bound eager equation in `enumerateOutWith_eager` is definitionally the old `enumerateOut`. The edge helper uses predecessor fuel for its child callback. Its eager specialization matches the old edge action at zero and successor bounds. The shallow selected-root path descends to the predecessor edge bound; terminal endpoints and nonordinary views use the old eager function at the current positive bound. The child helper allocates and installs the complete suspended list. No fixed callback budget is incorrectly retained across driver recursion.

The root renderer keeps hole zero when work remains. The public partial wrapper discards the stop status and uses the existing partial renderer at the stated finite bound. It does not turn holes into an acceptance certificate or discharge residual obligations. The literal `stop_all` statement requires a positive bound and the actual nonempty/all-accepted candidate facts. Its claimed unchanged state is consistent with the stop-before-scheduler branch.

## Limits of this clearance

The definitions explicitly use the existing modeled slot scan. They do not establish literal final-state equality with Haskell's cached scheduler. The graph's single recursive view still needs a source realization for both Mu and InternedUnion. These are disclosed source-refinement boundaries.

The no-stop identity-narrowing eager specialization has the correct callback and fuel arrangement for the planned bridge. It is not unrestricted equality with the old loop: the new empty precheck skips a callback that the old loop invoked. Arbitrary callbacks can change that slot. Even `ReadOnlyOracle` constrains only successful callback branches, so it cannot alone justify equality of full error lists. A successful-row bridge under the stated observing-callback assumption remains the appropriate first claim. The public shallow path also changes fragment observations and allocations; this review does not identify it with eager execution.

Root reported a harness path failure and a later running definitions check during this review. Those are Root-owned observations. This static clearance makes no compiler-result claim for either attempt or for the projection, definition lemmas, or main bridge.
