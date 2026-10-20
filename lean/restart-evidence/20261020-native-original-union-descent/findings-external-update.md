External Haskell documentation repair: 2026-10-20 22:30 CEST.
The remote branch `docs/binders-size-order` contains commit
`7469183231da3a9c7aefc115c9cc818f4867bd9d`. Its Typing.hs, README and
CHANGELOG patch qualifies size-major Binders ranks by the presence of a
subterm rule. It directs finite acyclic languages to upToSize. The commit
message reports the FixA/FixB example that motivated the follow-up below.
The exact source patch was inspected and saved in
`lean/restart-evidence/20261020-native-original-union-descent/upstream-binders-size-order-7469183.patch`.
This is an available external documentation repair. It is not imported
into formalize or main. No fresh matching-toolchain runtime check was run
locally. The earlier local reproduction remains unvalidated. All local
production Haskell files retain their bytes. Preserve the prior evidence
and repair registry below.

