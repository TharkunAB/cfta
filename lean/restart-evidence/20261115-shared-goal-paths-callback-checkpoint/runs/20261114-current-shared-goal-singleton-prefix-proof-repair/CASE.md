# Singleton prefix orientation and fold reduction repair

Frozen: 2026-11-14 23:22 CET. This candidate is uncompiled.
Source SHA-256:
`896c7640f3e95e93cf1f2449301eb8e63bb658aba4d3188e9aa087fd330ff6d1`.

The complete diagnostic log was inspected:
`20261114-fresh-goal-and-singleton-prefix-check/singleton-goal-prefix-1.txt`.
All four proof errors are addressed.

The stored-state equation from `success_pure` has the reverse orientation
to the local `published = united` fact, so this proof now takes its symmetry.
The final tuple equation likewise uses symmetry. The final state equation
already has `joined = published`, so the redundant symmetry is removed.
The shared fold simplification leaves only a concrete `ExceptT.run` over
one literal successful result; reflexivity now reduces that last match.

Both the private and public theorem headers are byte-identical to the
original candidate. No premise, source endpoint, caller, query, native
bound, operation, or conclusion changed. The original packet remains
unchanged and uncredited. Its CASE note retains the full scope and the
remaining root-site composition boundary.

Root owns compilation and publication. No compiler, live source, Git,
board, Haskell, or `/tmp` action occurred. No Haskell fix was found.
