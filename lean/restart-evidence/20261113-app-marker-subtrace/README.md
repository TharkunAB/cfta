# Private extraction of the actual application function read

The checked local observer takes the actual four-child `RequireAllReads` receipt.
Its recorded selected classes must equal `[[1],[2,0,0]]`. It extracts the function
`RequireNode(build [[0,0]])` and its actual `NodeReads`. The same input/output heap
and full memo endpoints remain in the conclusion. The other three values stay
unchanged. This statement does not assert that every application has this case.

The exact 15-line header is in `source-history.json`. The final 59-line source
is `source.lean.txt`. It is a private checked proof draft. No live library module
or public theorem is added. The source follows the same dependent memo receipt.
`cbv` proves the closed path calculation through checked equations.

Run `check.py` from any directory in the project Nix shell, under a serial scope
with 4 GiB memory.max and memory.high, zero swap and one Lean thread. It checks
the source hashes, performs four actual GNU zero-context patch replays, compiles
the same private proof and checks its axiom report. `checked.json` records the
executed check from `/tmp`. Only `propext` and `Quot.sound` occur.

The history retains five source stages and four rejected diagnostics. Direct
computation did not unfold the imported definitions. The final evaluator emits
proofs and adds no native-evaluation axiom.

The next missing link is the actual identity-row visit and its nested Type-child
read. The row prefix and suffix must retain their real heap and memo endpoints.
The observer does not supply that ancestry, finite-witness survival, a positive
minimum, a joint model or an accepted original-root completion. No Haskell,
Cabal or test-suite changes or Haskell repair are included.
