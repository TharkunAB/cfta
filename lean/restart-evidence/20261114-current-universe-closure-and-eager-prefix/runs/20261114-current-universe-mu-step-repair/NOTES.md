# Proof repair for the original Mu selected step

Status: UNCOMPILED REPAIR. The frozen original failed its private strict check.
This packet does not assign theorem credit to either version. Root remains the
sole compiler and live writer.

Date: 2026-11-14 19:05 CET.

## Input failure

Frozen original candidate SHA256:
`aab09cfcde92029cd9af621bee94a485c659be71a83fbf42edddca4dffc058b7`.

Exact failed log:

    lean/restart-evidence/20261114-next-composition-and-selected-replay-check/SourceSynthesisCurrentUniverseMuAtomInductionStep.txt

The original proof expanded `binder pattern` before using its local empty-list
equation. Its reverse-entry rewrite also encountered `initial.domains` and
`emptyDomain.key` instead of their literal let-normal forms. In both orientation
branches, expanding the general kernel body function similarly hid the local
`patternBody` equation behind a raw match. The strict log includes unused simp
arguments caused by those failed rewrites.

## Exact repair

Three proof blocks change:

1. State the full reverse-entry goal with the two binder lists explicitly. Keep
   `binder pattern` intact, rewrite it to `[]`, and then simplify the two list
   appends and the symmetric pair. Do not expand the general binder function.
2. In the right-Mu branch, change the actual intermediate expression to literal
   `domains`, `emptyKey` and the exact reached machine. Then rewrite the full
   reverse entry, the unexpanded `body pattern`, and the symmetric pair.
3. In the left-Mu branch, change the expression to the fixed original `entered`
   domain and exact reached machine. Keep `body pattern` intact and rewrite its
   local equation directly.

The new proof adds no hypothesis or semantic argument. The theorem header is
byte-identical to the original header. The literal original domain, actual
native branch, both operand orientations, full endpoint and fuel `n` M call
under the fuel `n+1` selected call all stay unchanged.

`minimal.patch` records the three proof-only changes. The original full and
coupled open headers are byte copies. Exact input and output hashes are in
`SOURCE-PINS.sha256` and `SHA256SUMS`.

## Boundary

No compiler, live module, Git, board or child operation was used. No old packet
was edited. The complete A/M theorem and full generated-Type atom theorem remain
open. This packet adds no Haskell change or fix.
