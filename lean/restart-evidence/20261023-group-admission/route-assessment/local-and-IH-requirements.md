Use the existing Fin.induction directly on the public all-boundaries conclusion. Do not add a global predicate, structure, private helper, generalized list execution producer, or typed local complete theorem.
For review only, write P(j) for the conjunction of At at (states j).checked and canonical returned-cell admission at (states j).memo. This notation is not a proposed Lean declaration.
The exact installed Fin.induction API takes motive : Fin(n+1) -> Sort, zero : motive 0, and succ : forall i : Fin n, motive i.castSucc -> motive i.succ. It returns forall i : Fin(n+1), motive i. The primary definition is Init/Data/Fin/Lemmas.lean:909-917.
Set n to entries.length. The only generated IH is P(index.castSucc), with all source/model/Room/chain parameters fixed. The successor goal is P(index.succ). There is no generalized current state or new fuel.
The zero obligation rewrites states 0 by start and uses the two initial certificates. For entries=[], Fin 0 supplies no successor. Fin 1 still contains the sole zero boundary.
The successor destructures the supplied input packet into its Stable, Good, SemanticReady, Trace and Idle fields. It destructures the IH into current At and canonical pair admission. These fields concern exactly states index.castSucc.
Prove the bucket equality inline, not through H22's private bucket_readback. A small set of typed local facts is sufficient:
1. reversed: Iteration for reverseTable of the original prepend table and entries mapped to each key with its reversed bucket. Its value comes from public iteration_reverse. This fact can be placed once before Fin.induction.
2. included: the pair consisting of (entries.get index).1 and (entries.get index).2.reverse belongs to that mapped entry list. Use List.get_mem and List.mem_map.
3. found: reverseTable of the prepend table, at that entry key, equals some of that reversed bucket. Use the public Iteration.lookup equivalence with included.
4. contents: (entries.get index).2.reverse equals nodeEdges parent filtered by the exact entry symbol. Rewrite found by reverse_fromRows and take the contents projection of public lookup_some.
These facts retain repeated row occurrences and exact row order. There is no nonempty-bucket premise, sorted-key premise or alternate iterator order.
Pass the same states index.castSucc, states index.succ, fuels index and kept index to H29 completed_admitted. Rewrite only the bucket control by contents. Pass the same parent membership, initialDomains/Valid, Room, input packet and IH certificates.
The adapter internally proves full after-state equality by completed_unique. The new chain theorem does not assume or repropose uniqueness and does not call an unrelated second scan.
The exact future declaration package must list the four local fact types, input-packet/IH destructured field types, Fin induction activation and generated IH. Any extra inferred have, let, obtain type, show, helper or induction must be reviewed before body authoring.
