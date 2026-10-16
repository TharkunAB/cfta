# Checked edge-body code inversion

Status: frozen. `SourceEqualityNativeDemandBodyYield.lean` has 57 lines. Its SHA-256 is `a9b38de0481de1a7736c8f54929e8c662eea942213faf51739da2ce5668dc8d5`.

`yielded_unbind` classifies the literal executed body branch. A yielded body with continuation `next` supplies code whose pure-body execution yields at the same full checked state. The original yielded control is exactly that code with `next` appended. Mismatch and rejected branches emit the sentinel code. An accepted conjunction emits the actual checked child code. Error and blocked branches cannot satisfy the yielded premise.

`pure_yielded_code` specializes this result to the pure continuation. It derives an ordinary code control. Neither theorem assumes physical readiness, word safety, clean code, a result law, or recursive completion. Neither needs a supplied `DecidableEq` instance.

The direct production check passes on the first attempt without diagnostics. The canonical `body-yield-build.log` passes with 1055 jobs. Its only warning is the historical unused `inputs` warning from `InternedFreshOrdinaryClosedCompletion.lean`.

The imported public probe checks both axiom/full-signature pairs with explicit types, proofs, universes, deep terms, and ten million print steps. `body-yield-public-1.log` passes without diagnostics or `sorryAx`.

Two integration kernels apply the inversion to actual branch equations. One derives the mismatch outcome without field or child premises. The other derives the accepted outcome from literal current field loads and the actual checked conjunction result. Both retain the exact operation state and the complete unchanged native state. The accepted kernel fixes the same guard equality instance used by the source body. It does not use an independently elaborated comparison instance.

`body-yield-kernels-4.log` checks both integration pairs without diagnostics or `sorryAx`. Earlier source snapshots and failed logs remain unchanged. Those attempts contain a deprecated simp name, a no-progress tactic, and the guard-instance mismatch. No production repair was required.

This is a code-shape inversion. It does not prove field readiness, child completion, query capacity, or a semantic result. No older production source, older evidence, Haskell file, Audit source, or Git state was changed.
