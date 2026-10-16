# Current raw reconstruction validation

Source: `MicroCFTA.SourceCurrentAllocatedRawRebuild` (191 lines).
SHA256: `ae539502618e66a7ac08b90ab57c315ae1b03853ed9ac9bc8926d9617f48f73a`.

`edge original children before` runs the literal raw makeEdge request and
advances the same full checked state. `edge_same_arity` identifies this
request with `EqualityLeafProjectionSetChildren.setChildren` for every
checked fallback when the child lengths agree. This is exactly the direct
branch in `cfta/src/Data/CFTA/Interned/Type.hs:391–400`. The theorem does not
assert an unchecked replacement implements the different-arity branch.

`edge_verified` derives the original raw FieldAvailable from the original
resident edge and the current physical annotation heap. It needs available
replacement children and the actual equal-length fact. It derives returned
Ready, At, Effects, machine Extension, edge residency, exact symbol/full raw
constraint/ordered children, and unchanged equality operations, native node
and edge tables, and domain table. It neither calls MkEdge nor demands a
new accessor. No original arity-admissibility or guard-acceptance law is an
input. `EdgeReceipt.language` gives the complete independent edge-language
equation for any guard interpretation, including PCS guards.

`modify` reuses only the literal pure `SourceEqualityPartialNodeRebuild.modify`
definition. It lifts its returned native state and retains equality operations.
The fast path compares ordered edge identities. Coherence, old node availability,
and new edge residency derive equality of complete row records on a hit.
The other branch runs the actual makeNode. `modify_verified` derives Ready,
At, physical effects, machine Extension, availability, and exact new-row union
language in both branches. It does not require closed original nodes, closed
new rows, a semantic answer callback, or historical native execution validity.
This matches `Interned/Type.hs:620–627` on an ordinary input.

Mu reconstruction boundary:

`Equality/Operations.hs:85` uses the bidirectional pattern `Mu`.
`Interned/Type.hs:674–676` reconstructs through `createMu`; it is not an
unconditional identity return. `SourceEqualityMuReconstruction.rebuild`
models both cached probe callbacks, filtering, the canonical request, and
cleanup. `completed` and `verified` require `Clean depth ordinary`.
`from_origins` derives Clean from `InternedFreshOrdinarySemanticOrigins.Heap`
and availability. Current Ready supplies coherence and availability, but
its SemanticReady includes Context/depth/guarded/budget heaps, not that
source-origin heap or the two probe NoSelf facts. No Ready-to-Clean bridge
was established here. A current binder graph must retain the literal actual
rebuild completion receipt and its returned heap until that invariant is derived.
No binder identity theorem was added.

Validation:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedRawRebuild.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedRawRebuild
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-inherited/raw-rebuild-public-probes.lean
```

Direct source terminal 0, no warnings (`raw-rebuild-direct-2.log`).
Focused canonical terminal 0, 1,236 jobs (`raw-rebuild-build-1.log`).
Only the existing unused `inputs` dependency warning appears.
Seven public axiom checks, four full signatures, and nine kernel examples
pass (`raw-rebuild-public-probes-3.log`). Only propext, Classical.choice,
and Quot.sound are reported. The kernel probes check fallback independence,
unchanged sidecars, exact resident edge replay, ordered unchanged/changed
modify branches, derived field availability, PCS edge meaning, open row-union
meaning, and empty-row rejection. No extra compiled evidence artifacts were made.

Public probe SHA256: `517ade97a2f405d1f9681a2c88c8b8be628b3ca1d9ee7bd5ce75df33008b2182`.
Final probe log SHA256: `5e7ed8b3d39bd34a49bc3f05c60fc7648125883f6f371609a7d2ed0f93072fbe`.
Source and API are frozen. No old proof source was edited.
