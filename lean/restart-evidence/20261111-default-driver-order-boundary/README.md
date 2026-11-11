# Eager and deferred enumeration have different orders

The public Haskell APIs return different orders for one finite ordinary grammar:
`r(f(a|b), c|d)`. No equality constraint or recursive node is present.

runsBy with constant zero weights returns ac, ad, bc, bd. termsPruneUntil
with Unit state, no preference, identity narrowing, no stop and a false
callback returns ac, bc, ad, bd. Here ac means r(f(a),c), and so on.
The concrete terms have the same multiset. Both counts are four. No eager
residual obligation or shallow hole remains.

repro.hs calls both actual public APIs. expected.txt contains the exact
observed output. source-hashes.json records the four primary Haskell sources.
check.py checks the source hashes, checks formatting, builds the library and
runs the reproduction in the project Nix environment. It requires the existing
serial 4 GiB heavy-management cap. Run it from any working directory.
No binary archive is required.

A successful check reproduces the ordering distinction. It does not prove
ordered equivalence. This is not a production bug. The two APIs use different
ordinary-child operations. A membership or multiset simulation can still be
possible. This fixture does not prove such a simulation for every grammar.

The shared Lean driver uses deferred ordinary children. This fixture excludes
a direct general ordered identification of the two Haskell expansion strategies.
It does not execute Lean or prove Lean/Haskell correspondence. The grammar is
not a synthesis Program fixture. Decoding would collapse the toy r term to
Var r. No claim about distinct decoded Program order or Sized rank APIs follows.
