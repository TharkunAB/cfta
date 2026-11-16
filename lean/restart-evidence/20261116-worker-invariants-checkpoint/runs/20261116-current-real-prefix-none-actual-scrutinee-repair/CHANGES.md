UNCOMPILED actual-scrutinee repair for strict21245 prefix diagnostics.
Fullc9e887 header and probe are byte-exact. Original44f8 and log stay unchanged.

1. The decoded-none branch has already rewritten read/check raw arrays to their
actual literal singletons. Supply those two literal snapshot proofs from the
already derived readGood/checkedGood. Do not try to unify their old raw index.
2. Reduce the known prepared done/some constructor before generalizing the raw
action. The failed log shows a residual match on done(...), so its branch-local
action_1 hides the actual action expression from generalize. One dsimp only does
beta/iota/zeta/projection reduction. It unfolds no algorithm and adds no fuel.
This also removes the false prepared-case split behind the three later errors.

All actual operation proofs, array/candidate/state receipts, other body bytes,
initial-only premises, checking limit and original six runtime fuels stay exact.
