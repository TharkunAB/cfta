# Original identity resources: current heap and actual preparation receipt repair

Status: UNCOMPILED. No full-worker proof credit is claimed.

The preceding 609-line candidate failed in Root's strict check. Its log is `../20261116-native-identity-verified-components-check/0-20261116-real-callback-and-isolation-checkpoint-work.txt`. Its original source, hash a9cd0276e22b09fce0e6f7247c57ba976a1ef22cf53e9a8e98a3520b9ec9f3b8, remains unchanged. The log contains actual heap mismatches, an unknown iteration lemma, incomplete preparation-branch reductions, and two later 2M timeouts. Printed probes after that failed elaboration give no full-worker proof credit.

Only the successful-preparation proof changes in this packet. All other declaration headers, component proofs, supplied budgets, and probes remain byte-exact.

The proof now derives preparedFitsAt, preparedKnownAt, and availableAt once for the actual prepared caller. It uses the verified caller heap projection and verified prepared-seed alphabet projection. Both the ordinary and opaque branches consume these exact facts. The height and row-shape calls also use availability at the prepared caller heap.

The nonexistent iterate_index_le call is replaced with a direct proof. The actual selected row length is at most limit. Nat.exists_eq_add_of_le supplies the remaining count. The existing FiniteReservation.iterate_add and iterate_ge lemmas then prove profile and alphabet inclusion. No iteration resource or result hypothesis is added.

After rewriting the actual SelectedPreparation.run equation in the opaque runtime proof, dsimp only now reduces the concrete returned pair and singleton list before the Bool and Value case splits. Those splits therefore act on the actual returned bucket and value. The earlier proof split while the corresponding values were still bound inside an unreduced match.

The checked small alphabet and resume-preparation helpers remain unchanged and occur once. The prepared wrapper, Empty proof, main depth induction, and public projection remain unchanged from the preceding candidate. The original public declaration c831, public header18d8, internal fd94, prepared3448, successful f784, and Empty57d2 remain byte-exact. The proof-checking limit remains 2M everywhere. No runtime fuel, recursive depth, reservation, forecast, callback, outcome case, or earlier emission was changed.

Use the current owner with the existing seven task/scan/opaque source fragments. Prepend IMPORTS if needed. Append ONLY this APPEND.lean.txt. Retain the 66 original and seven existing component probes. Append ALL-NEW-PROBES.lean.txt, which is unchanged and contains eight axiom probes. Do not append an older consumer or the separate small-helper packet. The owner plus this probe set should produce 81 reports when the complete check succeeds.

No live Source, compiler, Git, board, root documentation, Haskell, or temporary-directory action was performed. The original whole-worker resource theorem, real-narrow coverage, source native-request admission, and full compatible finite accepted-completion objective remain open.
