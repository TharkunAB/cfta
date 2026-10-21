# First ordinary check and exact repair

Root observed owned PTY 68824 terminate with exit 1.
The complete input and 186-line raw log remain in finite-calls-strict-1.*.
The effective cap was 4 GiB with no swap. Declaration limits did not change.

Entry accepted Caller width. Origins requires Caller (bits + 2).
The failed declaration caused error-recovery warnings in later proofs.
The log also reports deprecated if_neg and if_pos names.
The source contains no sorry term. The failed output is not accepted.

The repair changes four source lines. It gives private Entry a bits binder
and uses Caller (bits + 2). It replaces if_neg with ite_eq_right and if_pos
with ite_eq_left. Installed Lean Init/Core.lean lines 1179–1194 define those
replacement theorems and the deprecated aliases.

Original: 236 lines, 32cfa9e1a229237dcaf683fe77f588cb2eeb541929f7e4dff33ef2809370183c.
Repaired: 236 lines, 84e7803898495e956335917802621bb616585f3ff223274809c3eba182c431cc.
The public 35-line header and first 22 context lines do not change.
The original author, source review, provisional preservation preparation
and unused provisional FULL preparation remain unchanged.

No limit or linter exception is added. A separate repair review and fresh
ordinary compiler check are required. No Haskell source changes.
