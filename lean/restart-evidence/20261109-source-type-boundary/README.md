# Raw and reduced synthesis Type annotations

This replay uses the public synthesis API in all three encodings. The library
has `f : a`. The query has `x : A` and goal `B`. The requested size is two.
The raw space accepts the explicit finite witness with `f : A -> B`.
Its partial run truncates the Type annotation of `f`. The reduced space
exposes that annotation as `A -> B`. Both paths decode to `f x`.
The normal generator has cardinality one and returns that program.

The raw source permits an opaque Type child with descendant constraints.
Source field roles alone cannot prove full child-bucket retention. This
example does not establish a defect in reduced synthesis or its generator.
See `audit.md` for the remaining formal preparation obligation.

Run from any directory under the serial heavy-management 4 GiB cap:

```sh
python3 /home/tritlo/Code/mcfta/lean/restart-evidence/20261109-source-type-boundary/check.py
```

The checker builds the current generator offline with one Cabal job in the
project Nix environment. It checks formatting and the full replay output.
It stores hashes and effective cgroup limits. It stores no build archives.
