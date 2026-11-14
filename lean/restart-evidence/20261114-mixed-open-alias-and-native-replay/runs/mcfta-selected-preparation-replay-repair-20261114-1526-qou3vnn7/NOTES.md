# Selected-preparation replay proof repair

Status: UNCOMPILED. No new proof credit. Root owns compilation and live writes.

Check1 reached the final representative-bind rewrite inside `unenumerated.some`. Its target still contained `match UVarValue.unenumerated (some _handle) _bucket with ...`. The old and new representative observations were already exact. The rewrite could not find the representative bind beneath that unreduced match.

The repair adds ONE `dsimp only` immediately before the failing rewrite. It reduces the known UVarValue/Option match and exposes the representative bind. The original two exact representative rewrites then apply to the same continuation. No operation or proof premise changes.

Both theorem headers and the entire second main proof remain byte-for-byte identical to ca7dd717. Every other original module byte remains identical. `proof-only-repair.patch` shows the single added tactic line. `candidate.patch` adds the complete repaired standalone module. The original frozen ca7dd717 packet remains unchanged. The terminal failed check1 diagnostic is retained, including its inherited sorryAx reports; those reports receive no proof credit.

The same checked SelectedValue replay dependency and import graph apply. No compiler, Nix/Lake/heavy job, live source mutation, Git operation, board request, or child task was used. Hash/header/one-line checks are preparation checks only.

After validation, pointwise preparation resources must be derived from this actual replay and `complete_resources_current`. No phase or future result/resource provider may be added. All-workFuel stopped-output history, ONE finite accepted original-root common term/assignment, parked backward recompletion, and all original typing/LPO/language/stream/count/weight/rank/runtime clauses remain OPEN.
