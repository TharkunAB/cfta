# Prepend grouping body proposal
Status: COMPLETE SOURCE-ONLY, UNCOMPILED, HOLD FOR WHOLE-SOURCE REVIEW.
The whole proposal has85 ordinary lines: three definitions, six public theorems and no private helpers. It has one generalized-table list induction and no extra local lemma statement.
All exact approved headers and context are unchanged. Removing the definition/proof bodies recovers the approved49-line declaration inventory byte-for-byte. All three definition equations match.
The one-step law is singleton-only. The fold retains arbitrary initial optional entries. Iteration transport uses the actual Option.map witness and literal list-map membership; it needs no new inversion helper.
The final theorem reuses the existing Iteration.permutation after the empty-fold bridge. No key order or heap equality across iteration orders is asserted.
None and Some [] remain distinct. Repeated rows and prior buckets remain. No new Item equality instance, callback, source assumption or container implementation is added.
The source is below the estimate because the existing finite iterator fields and Option.map_eq_some_iff give a direct proof. No blank lines were removed to meet a limit.
I read all85 source lines and checked all header/equation inverses and live indexed source bytes. Lean elaboration and linters remain unchecked; root owns every check.
No compiler, prepared tool, runtime, Git, network or repository write ran. The only writes create this external proposal package.
HashMap refinement, stateful group traversal, symbol-only instantiation, Mu reconstruction and the whole public pass remain later work. Newer local commits have no push approval.
