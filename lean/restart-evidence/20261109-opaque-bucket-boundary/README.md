# Opaque descendant bucket and public truncation boundary

The public fixture uses the closed recursive union `b | mu X.(a | p(X))`.
The root has children `[union, a]` and equality paths `[[0,0],[1]]`.
The pruning callback retains every branch. The fixture uses public APIs.

The public replay returns `r(Mu,a)`. The explicit truncation API returns
`TruncatedRecursion` at the same position. Recognition rejects the proposed
bad ground term `r(b,a)` and accepts `r(p(a),a)`. The replay does not emit the
bad term. Exposing one layer of the child produces the valid concrete term.
Recognition also rejects the marker term. That fact does not establish a
concrete enumeration or synthesis defect: the API returns a truncation.

The internal branch allocates opaque nonterminal children with an empty
suspended bucket. The checked shared-child language laws describe that
retained bucket. They do not restore every supplied descendant constraint.
The generic assignment candidate in audit.md still lacks a checked native
Context witness. The audit was written before the public replay. Its public
fixture section is a proposal; repro.hs and observed.txt record the replay.
Accepted-synthesis reachability and a Haskell repair remain unestablished.

Reproduce from any working directory under the existing serial 4 GiB
heavy-management cap:

```sh
python3 /path/to/cfta/lean/restart-evidence/20261109-opaque-bucket-boundary/check.py
```

The checker verifies the source hashes. It builds the current library with
Cabal offline in the project Nix environment with GMP. It then runs repro.hs
and compares the complete output with observed.txt. It records no library
archive or build tree in this packet. checked.json records the replay.
