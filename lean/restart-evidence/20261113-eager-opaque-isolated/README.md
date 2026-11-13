# Opaque resources with original isolated slots

The eager resource source has 7032 lines, SHA256
`35418335bc33bd7b6d322deadcf49047da45b275e9eb70c36d9846226f4d5a52`.
The five existing public declarations and their proof bodies remain exact.
This cut adds no public theorem.

The new private predicate retains Program roles and each original isolated
pending slot that differs from the selected write target. The new private
opaque composition proves that property, conditional on the full lower-depth
`EagerProgramResumeWithIsolatedComplete` premise. The whole induction remains
open. `Ready` does not exclude an isolated selected target. The final full
Resume contract is unchanged.

The proof uses the same opaque producer and its actual `FinalizationAt` receipt.
The public shared-child observer preserves the same original marker through
the child. The actual finalizer preserves it at a different write target.
The native Post transports the same handle lookup. One recorded callback
then preserves that marker and the Program roles. All resource fields,
profiles, fallback plans and all-larger-fuel equations remain intact.
No second worker, independently chosen endpoint or future model is supplied.

[source-history.json](source-history.json) stores a zero-context reverse patch.
The checker actually applies that patch with GNU patch and fuzz disabled.
It restores the exact 6861-line source at
`c35b242b5fd2947553ced68243fd19a4cfc38ce6`.
The first strict check and the own-module build pass. The exact five-name axiom
report accepts only `propext`, `Classical.choice` and `Quot.sound`.
The combined six-module frontier also passes in the adjacent compatibility packet.

From the repository root, run the standalone checker in the existing serial
Nix 4 GiB max/high scope, with swap 0 and one Lean thread:

```sh
python3 lean/restart-evidence/20261113-eager-opaque-isolated/check.py
```

Whole eager-marker retention, finite Type model construction, original input
typing and the remaining full-system obligations stay open. No Haskell/Cabal
or test-suite file changes are part of this proof.
