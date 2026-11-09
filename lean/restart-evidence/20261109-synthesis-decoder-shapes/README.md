# Synthesis decoder shapes

The current public FirstOrder input had one component named filter. Its
annotation was the Type constructor app(A,B). At source component size 1,
the raw language accepted one typed term. The old decoder returned App A B,
with two component occurrences. The exact generator count was still 1.
before.json records the actual pre-fix run, source hash, Git source trees,
public input and reproduction code. It needs no source-tree archive.

The decoder now matches the generated application and filter layouts at
exact arities 4 and 2. Unary component and query argument rows retain their
names. The existing SynthesisSpec checks both roles in FirstOrder and both
Curried modes. It checks enumeration, generator values and counts. It also
checks ordinary application in all three encodings. tests.json records the
Synthesis group run and exact source hashes.

Run check.py under the existing serial 4 GiB/swap0 cap from any directory.
It uses the project Nix shell with GMP, rebuilds the current libraries,
reproduces the original public input with its repaired expected result,
and verifies source hashes before and after. Its temporary Main is removed.
The current Cabal project selects GHC 9.14.1. The package IDs come from its
inplace library database.

This regression establishes the concrete decoder repair. It does not prove
all source projection, component-size transport, driver completeness,
signed sparse execution, native capacity or Haskell correspondence.
