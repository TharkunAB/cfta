# Proof-only parser and reset repair

Status: UNCOMPILED. This packet has no proof credit.

The original candidate and failed compiler log remain unchanged. The compiler rejected the proof-local identifier `universe` because Lean reserves it. The repair names that local value `universeValue`. It changes all four occurrences.

The failed reset proof also exposed `active` through the local request abbreviation. The repair changes that local fact to `domain.key.free.isEmpty = false` before simplification. It preserves the existing reset argument.

The complete public header is byte-exact. The repair changes no source premise, child callback, count bound, original fuel, allocation receipt, or endpoint. All other proof text is unchanged. The final constructor cases still require a compiler check after the parser repair.

The source case ledger and scope remain in the original packet. The full native C/M history theorem remains unproved. There are no Haskell changes.
