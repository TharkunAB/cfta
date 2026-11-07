# Required arguments bypass the documented size-two head ban

The current public Synthesis API reproduces a discrepancy with Library.libraryAvoid. The documentation says: "With Nothing, the functions head no term of size two."

The reproducer uses the public library constructor. It gives f the type Int -> Int, bans f with Nothing, and asks for Int from a required argument x :: Int at size two. solutionsOfSize returns a representative that expand maps to f x. No private enumeration state is supplied.

The final bounded observations are:

- Required x with the ban: Just True for membership of f x.
- Component x with the same ban and no required argument: Just False.
- Required x without the ban: Just True.

The membership check searches the complete small solution list. All three observations completed within their ten-second limits. The problem is not inferred from a timeout. The local generator library built with GHC 9.14.1 -O0 in a project-derived Nix shell with GMP. fourmolu formatted the reproducer. cabal-gild checked cfta-generator.cabal without changes. This is one integration reproducer, not a full suite or CI run.

Source cause: buildTerms applies size-two pruning rules, but nonempty buildRelevant uses its generic split loop. Its empty function selection reads the size-one terms cell and admits f again. The FirstOrder construction port retains this current behavior. The behavior preserves Hectare program spaces. PR #203 proposes a documentation correction for the required-argument exception: https://github.com/TharkunAB/cfta/pull/203. It was open at 2026-11-07 18:09 CET. The earlier recommendation for a behavior change was too strong. Keep the source behavior and its faithful port. No production Haskell fix was made.

Reproduce from the repository root, serially:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus CAPPED_UNIT=mcfta-synthesis-required-argument-avoid HEAVY_PEAKS=/tmp/mcfta-proof-peaks.tsv /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 python3 lean/restart-evidence/20261107-synthesis-required-argument-avoid/check.py
```

observed.json records the exact source hash and source trees. The checker records outputs, so a later repair can change the first observation. No build archive is needed.
