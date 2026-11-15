# Boolean reduction repair

2026-11-15 01:13:09 CET. Uncompiled.

The prior source and diagnostic remain unchanged. The only proof change adds `Bool.false_eq_true` and `ite_false` to `checkExact`. These lemmas reduce the literal false condition before the pure result. All theorem headers and proof premises remain identical. The original CASE in `20261115-current-source-first-real-prefix-draft` states the full scope and remaining operations.

The previous check failed only at the unnormalized false condition. The printed `sorryAx` came from that failed check. This packet has no proof credit until Root validates it.
