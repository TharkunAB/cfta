# Checked parent-edge constructor validation

Source module: `MicroCFTA.SourceCurrentAllocatedMkEdge`.
Source SHA256: `edef55c0db42605c003a897b8637fc5bb26aba6fb922c1e8548eb67eb30c865b`.

The source check is `cfta/src/Data/CFTA/Interned/Type.hs:566–568`.
It tests raw contradiction before the child-list length and equality accessor.
The Lean wrapper executes the existing literal `SourceEqualityMkEdgeAllocation.build`.
It advances the full checked state with the returned heap and equality operations.
Both native tables and the domain cache remain unchanged.

`finite` needs initial class-scan Ready, inventory At, stored-value Ready,
raw FieldAvailable, and available completed children. It derives the exact
actual return, full physical effects, returned readiness, inventory retention,
machine extension, edge residency, and accepted-or-sentinel field equations.
It does not assume original arity admissibility or a universal Top field.

`reject` has no child-list parameter. `reject_correct` needs only initial
Ready and At. It derives the sentinel's Top field from its actual allocation.
`build_contradictory` equates the full constructor to this endpoint without
any child-availability or stored-readiness premise. This is an equation in
the completed resident model. It is not a theorem about evaluating a GHC bottom.

`Receipt.language` proves the total independent PCS edge-language equation
for the original raw constraint and supplied ordered children. In a rejected
branch, a hypothetical satisfying term would force the actual constructor
check to accept at that child arity. This contradicts rejection. The proof
uses stored-value Ready to derive active equality classes. It does not assume
the edge-language conclusion or a successful arity test.

Validation commands:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedMkEdge.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedMkEdge
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-local-reduction/mkedge-public-probes.lean
```

Direct source check: terminal 0, no warnings (`mkedge-direct-3.log`).
Focused Lake check: terminal 0, 1,234 jobs (`mkedge-build-1.log`).
Only the existing unused `inputs` dependency warning appears.
Public probe: terminal 0, seven public axiom checks, four full signatures,
and eight kernel examples (`mkedge-public-probes-1.log`). The only reported
foundations are `propext`, `Classical.choice`, and `Quot.sound`.
The kernels include raw contradiction, Bottom, cold Top allocation,
derived Top availability, unchanged native tables, generic sentinel emptiness,
arity-rejected child readback, and total PCS language composition.

Pending runtime transfers remain explicit: GHC forcing and lazy field demand,
actual mutable interner publication, machine identity capacity, and native map
representation. No global runtime schedule or outer reduction termination is proved.
The source and public API are frozen. No old proof source was edited.
