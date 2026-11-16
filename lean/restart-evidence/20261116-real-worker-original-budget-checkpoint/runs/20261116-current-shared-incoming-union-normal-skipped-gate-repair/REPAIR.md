# Skipped shared gate normalization

UNCOMPILED proof-only repair. The first candidate failed its strict check. It has no proof credit.

The preserved diagnostic is `lean/restart-evidence/20261116-native-shared-incoming-union-normal-check/shared-incoming-union-normal.txt`.

The skipped outcome completes with the literal Boolean false. The existing proof exposed that value but left `if false = true then .empty else query` in the encodeNode scrutinee. The repair inserts `simp only [Bool.false_eq_true, ite_false]` before splitting the actual encoded query. All other proof text is byte-exact. The full public header and appendable probes are byte-exact. No premise or original budget changed.

The original audit and candidate remain in `20261116-current-shared-incoming-union-normal-endpoint-draft`. README here retains that audit and its original candidate description; the repaired candidate has100 lines. No compilation or live source change was performed here. Root must run the next strict check.
