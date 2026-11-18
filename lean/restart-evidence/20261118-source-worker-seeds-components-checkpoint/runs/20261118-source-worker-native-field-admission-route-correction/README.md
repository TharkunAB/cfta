# Native request resource composition candidate

This packet corrects one historical audit statement. It also supplies one
UNCOMPILED same-owner EOF candidate. Read AUDIT.md for the actual worker gap.

Assembly order:

1. Prepend IMPORTS.lean.txt to the exact normal SeedClosure owner pinned here.
2. Keep all 23,529 old owner bytes contiguous at offset 61.
3. Append APPEND.lean.txt.
4. Append PROBES.lean.txt only in the compiler fixture.

SourceCurrentNativeNumericalSeedClosure.lean stores the exact source assembly.
ASSEMBLY.json records its hashes and counts. FIRST-HEADER.lean.txt was written
and pinned before PROOF.lean.txt. The original owner and prior audit remain
unchanged. No proof limits, axioms, linter settings or runtime code are added.
Root owns all compiler, normal Source and publication actions.
