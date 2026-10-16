# Checked local parent-edge validation

Source module: `MicroCFTA.SourceCurrentAllocatedParentEdge`.
Source SHA256: `415caf6fc59d1c04d64ae93c51e4932c26e8031c84733e3caa622cbb5e008549`.

Source order: `cfta/src/Data/CFTA/Equality/Operations.hs:164–168` passes the
local child reduction as the child argument to `mkEdge`. The constructor
tests raw contradiction first (`Interned/Type.hs:566–568`). The parent graph
records that branch before local reduction. The live branch records the
actual current local graph and the literal checked constructor return.

`rejected` requires raw contradiction, initial Ready and At, and the current
merge/fourth/global memo invariants. It has no load, Cached, stored-value
Ready, child availability, inherited Ready, local ranges, or local completion
premise. Its returned graph, read receipt, sentinel allocation, physical
effects, inventory, and memo invariants are derived.

`finite` also handles the live branch. Its inputs include the actual initial
field load, normalized original field, inherited Ready, available original
children, and initial warm memo invariants. Its range plan is conditional:
only raw contradiction=false requires the current local range plan.
Local completion derives the exact actual returned children and state.
The original stored field and its load grow to that returned operation cache.
The checked constructor then runs at that state. No operation table is reset.

The Receipt retains Ready, At, physical Effects, returned edge residency,
merge Stored and language coverage, merge and fourth entry retention,
global table validity, and fourth semantic correctness. Its construction
field distinguishes an exact rejection receipt from a live local return
followed by an exact `mkEdge` receipt. Local child length equals original
child length. The final sentinel can instead have one empty child. The
theorem does not assert unconditional final-edge arity preservation.

The language theorem proves unconditional narrowing to the original raw
edge language. It proves equivalence under the actual inherited payload's
PCS satisfaction. Empty child erasure alone does not refute a zero-child
forest; raw contradiction and the actual constructor supply the needed
edge rejection. No accepted candidate or desired result law is an input.

Commands:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedParentEdge.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedParentEdge
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-local-reduction/parent-edge-public-probes.lean
```

Direct source: terminal 0, no warnings (`parent-edge-direct-3.log`).
Focused Lake: terminal 0, 1,390 jobs (`parent-edge-build-1.log`).
Only the old unused `inputs` dependency warning appears.
Public probes: terminal 0 (`parent-edge-public-probes-1.log`).
Three public axiom checks, four full signatures, and seven kernel examples pass.
Only `propext`, `Classical.choice`, and `Quot.sound` appear.
Kernels check the raw no-local branch, zero-child raw language, rejection
memo/inventory retention without child assumptions, exact sentinel/arity
alternatives, narrowing, conditional equivalence, and unchanged rejected
native tables with the literal grown equality operation cache.

Remaining boundaries: current local range checks remain explicit. The
outer `reduceChildren` continuation at `Equality/Operations.hs:93–96`
still combines inherited first and the returned edge accessor second,
descends by child index, and recursively calls the outer worker. This
module does not prove that recursive caller's completion. It does not
model the separate reduced-edge cache, GHC forcing, runtime publication,
machine identity capacity, or native mutable map implementations.
These completed serial graphs do not establish a literal executable-worker
or GHC demand adapter. The source and public API are frozen.
