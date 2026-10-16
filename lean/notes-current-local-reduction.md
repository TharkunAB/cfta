# Warm local reduction and checked parent construction

Source main is `8f85ddb6`. The preceding published checkpoint is `af0b0fa9`.
Proof commits are `cb5232fe`, `8f38d731`, `9432d30d`, and `c2cfe5c8`.
No Haskell implementation or test file changes. Root FINDINGS.md retains
the external Haskell fix registry first.

## Actual warm precheck

`SourceCurrentAllocatedPrecheck.state` runs the literal allocated accessor
and precheck at the current operation state. It retains the complete native
state. `loaded_complete` derives every branch from the actual field load,
original normalized field, inherited Ready, and current Ready and At.
`complete` derives the load from FieldAvailable. `resident_complete` derives
FieldAvailable from the actual resident edge.

The receipt has exact physical own readback, the actual operation return,
Valid, Grows, physical Effects, machine Extension, Ready, and At. It derives
the unchanged, contradictory, and live branch meanings. Live records retain
the original physical order, proper paths, coherent ascending tries, and
nontrivial path classes. The unchanged branch has two empty equality
payloads. Its preceding accessor can still allocate equality values.

## One Scan and its actual continuation

`SourceCurrentConjunctionScanClassPass.Reduction` records one actual current
Scan. A stopped Scan erases the original child slots. A successful Scan
records exact positional retained records, the literal requireAll return,
and the complete current checked class pass at that return.

`Reads` threads each actual global bundle through Scan, required execution,
and the pass. `Ranges` requests class ranges only at actual successful Scan
and required-worker prefixes. It does not ask for a future Ready state or
a result-language law. `from_scan` retains a supplied actual Scan.
`finite` constructs the Scan and its continuation from initial invariants.

The receipt derives final Ready, At, physical Effects, available original
and returned forests, exact child count, merge Stored and coverage,
retained merge entries, global validity, fourth correctness, and retained
fourth entries. A stopped result refutes one original class on any accepted
original forest. The successful result narrows the original language and
retains every term satisfying the original classes. No blanket native
Extension is inferred from physical Effects alone.

## Complete local child graph

`SourceCurrentAllocatedLocalReduction.Reduction` selects unchanged children,
empty children, or the Scan continuation using the literal allocated
precheck result. All branches use the actual returned operation state.
`Reads` adds no global query on early returns. `Ranges` requests Scan ranges
only at the actual live precheck branch.

`finite` supplies no successful future worker, callback, admission oracle,
or language receipt. It constructs the raw graph and all stage reads.
Its receipt narrows the original forest. If a term satisfies the original
full PCS guard and inherited equalities, input and output membership agree.
An erased zero-child forest is still the empty forest. The contradiction
law refutes the conjunction of the full guard and inherited payload.
It does not incorrectly declare that forest language empty.

## Actual checked parent constructor

`SourceCurrentAllocatedMkEdge.build` wraps the literal allocated source
constructor. `finite` returns actual constructor effects and the exact
accepted or sentinel fields. It derives stored activity from stored Ready.
FieldAvailable alone does not imply constructor acceptance.

`reject` has no child-list parameter. `reject_correct` needs only Ready and
At and derives the sentinel's Top field at the current operation cache.
`build_contradictory` relates the completed-list constructor to that branch.
Both native tables and the domain cache remain unchanged by this constructor.
Its language theorem covers accepted and arity-rejected results under
independent PCS meaning.

`SourceCurrentAllocatedParentEdge.Edge` tests the original raw contradiction
before any local child graph. The public `rejected` endpoint needs no load,
Cached, inherited Ready, child availability, or local range premise. A live
edge executes the actual local graph and then checked mkEdge at its literal
return. The original stored field grows to that cache before constructor use.

The parent receipt derives actual returned edge residency and full physical,
inventory, merge, global, and fourth invariants. It proves unconditional
narrowing to the original raw edge language and equivalence under inherited
PCS satisfaction. It does not assume candidate acceptance or the intended
result law. Its construction field distinguishes exact sentinel rejection
from checked construction on the actual local children.

Local children retain original arity. A sentinel has one empty child and
Top, so no unconditional final-edge arity law follows. Source
`Equality/Operations.hs:93–96` must next read the returned edge. It combines
inherited FIRST and returned own SECOND. This key order differs from local
precheck. Source `Interned/Type.hs:391–400` uses raw interning for the later
same-arity setChildren; that step is not this checked mkEdge call.

## Validation and preservation

Pinned Lean 4.34.1 passes the full Audit: 2363 jobs and 56924 theorem
dependency checks. Only the standard three foundations and the old unused
input warning occur. Focused builds, public signature and axiom probes,
and independent reviews pass. External kernels check zero-child erasure,
raw rejection without child assumptions, actual sentinel fields, exact
constructor meaning, resident edge entry, and two sequential warm edges.

The two-edge kernel derives initial field loads and children from resident
records. Its second call uses the first call's actual returned state,
inventory, equality operations, merge table, fourth table, and global bundle.
No future readiness or cold reset is supplied.

Evidence and frozen sources are in
`restart-evidence/20261016-current-local-reduction/`. All 4060 starting files
remain. All 2357 older non-Audit proof sources retain identical bytes.
Eighteen frozen manifests, stashes, other worktree records, and the Haskell
fix registry remain. Earlier unavailable external drafts are not claimed
recovered or reverified. Unchanged Haskell validation reuses the strict Nix
all-component build, 777 examples plus golden, five-file Fourmolu, and
four-package Cabal-gild.

## Remaining source and library obligations

Read `inherited-current-next.md` in the evidence directory. Next construct
the CURRENT inherited prefix once from the actual returned edge, then its
indexed descents and recursive requests. The old childInheritance allocation
core has useful local semantic laws. Mapping that whole helper over children
would repeat combination and would not match this source schedule.

General constrained recursive completion remains open. Source comments
retain unequal-length classes as unproved. Local finite completion supplies
no decreasing measure for narrowed recursive children. Ordered ordinary
rows, literal modifyNode, and the current outer and edge result caches also
need composition with these new bodies.

These are completed serial graphs. They do not prove the literal bounded
class worker or the host demand schedule. Actual GHC initialization, lazy
IntMap and list demand, the noConstraint CAF adapter, pending publication,
concurrency, identity lifetime, physical containers, machine capacity,
solver IO, random draws, callbacks, and codecs retain explicit boundaries.
All broader frontend, recursive generator, separate Sized, and older
constructor and equality targets remain active. Preserve the optimized
interned core. This checkpoint is progress toward the full library goal.
