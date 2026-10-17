# Measured memo-aware Merge graph review

Frozen on 2026-10-17. The production source is `lean/MicroCFTA/SourceCurrentMemoMergeMeasured.lean`.
Its SHA-256 is `ce490fca71ddbccc797ccd99b0f6f9e07b0eaabef41564e568703f5d031a9906`.

The two mutual measured relations retain the exact code, initial heap, initial memo, returned value, returned heap, and returned memo of the supplied actual graph. Pure, Work, selection, and warm call cases cost one. A request adds one to its child call. Bind adds both executed stage costs and one. A miss adds one to its complete body cost. Both erasure theorems preserve all graph indices. Both graph conversion theorems construct a finite cost from the supplied graph.

SelectionReady and CallSelectionReady are proof-indexed relations. They require the same selection fuel only at the selections that the actual graph reaches. Each selection certificate returns the same ordered values and full heap as the original local receipt. Bind requires certificates for both actual stages. Requests require their exact child certificate. Hits require no body certificate.

Replay uses strong induction on the additive cost. Each recursive worker call receives the same residual worker fuel. The sum used for Bind is conservative and pays for both stages. Selection replay uses the existing selection stability theorem. It preserves the full returned heap. Miss replay runs the same actual body, then reads the winner from that body's current memo and applies the literal keep-first remember function. It does not identify the candidate with a different current winner.

The imported public probe checks all ten public declarations with full explicit signatures and axiom reports. The only reported axioms are propext, Classical.choice, and Quot.sound. The final kernel probe checks three declarations with the same settings.

The nested_misses kernel builds an ordinary node with a nonempty child node from the empty constructor state. Its own literal worker execution starts from an empty Merge memo, executes nested child and parent misses, and publishes both cells. The enclosing actual Code then executes a selection. Graph conversion and replay retain that exact return at arbitrary extra worker and selection fuel. No completed graph is supplied to the kernel.

The warm_hit kernel starts its second call at the first call's exact returned heap and memo. It reads the produced parent cell at any positive worker fuel and any selection fuel. The returned heap and memo stay exact.

The current_winner kernel uses the actual published parent cell. It proves that the parent is nonempty and that a distinct Empty candidate cannot replace the current winner. This kernel tests keep-first publication after an actual nested call. It does not construct a miss body whose candidate loses to a nested publication at the same key.

Strict production attempt 4 passed with an empty log. Canonical build 1 passed with 786 jobs. Its warning belongs to the earlier InternedFreshOrdinaryClosedCompletion dependency. The new production source and the final imported probes have no warnings. Public attempt 1 and kernel attempt 8 passed. Earlier failed sources and raw logs remain in this directory. Kernel attempt 3 records an invalid command invocation. Kernel attempts 4 and 5 used the same fixture while the proof of full memo equality and the dependent readiness recursor were being corrected. Attempts 6 and 7 isolated the final constructor inequality proof. The final source uses explicit unfolding for the literal worker equalities and direct mutual recursors for readiness.

This module is a completed-graph replay component. SelectionReady remains an explicit local selection receipt premise in the public replay theorem. The kernel derives one shared bound from its finite actual selectors; it does not derive an initial general Merge bound. The initial-only general recursive Merge resource producer, whole selected reduction resource argument, and whole-library convergence claim remain outside this component.
