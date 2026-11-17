# Public actual-reader export

Status: FROZEN UNCOMPILED. Root owns all compilation and Source installation.

The assembled `SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.lean`
contains the entire old owner as its exact byte prefix at offset zero.
Its sole suffix is `APPEND.lean.txt`. No new import is required.
Compile that assembled module with the separate `PROBES.lean.txt` suffix.
The normal owner and every previous packet remain unchanged.

The public header changes only the private declaration's visibility and name.
The body directly calls the existing private child_at_reader proof.
There is one new public axiom probe. The normal default proof limit applies.
No checking cap, linter option, runtime fuel, or observation budget changes.
