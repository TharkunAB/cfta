# Native row histories and remaining recursive provenance

Starting checkpoint: 0068ade6. Proof commit: f1f77bf1.
Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.
Read [the proof status](notes-proof-status-20261017.md) for the full target.

## Checked additions

| Module | Result | Boundary |
| --- | --- | --- |
| NativeRowOrigins | Each indexed result retains its exact request, ordered prefix and suffix, and complete input and output states. Ordinary output rows select original indexed left and right rows. Accepted edge bodies retain the literal conjunction guard and actual ordered child calls. Union epsilon rows select an indexed member result and its actual call. | These are laws about actual successful physical traces. They do not construct general outer completion. A warm edge request is retained, but its earlier writer's complete guard provenance remains open. |
| NativeInputExchange | Actual raw result absence derives agreement on surviving varying input names. A later complete semantic cache constructs the changed full source run with the same value. Fixed captured values can contain arbitrary available nested Mu records. | The absent name must be free-absent in the raw result. Normalized callback no-deep absence alone does not imply this premise. The later cache supplies its own Context, depth heap, and coverage. |
| RequiredUnionNormalNative | Actual native callbacks, optional binders, admitted primitive Work, checked instructions, bounded execution, physical prefixes, and allocated queries retain union normality on every stopping outcome. | Arbitrary Work code needs physical instruction admission. This invariant does not establish language correctness, readiness, or completion. |
| RequiredUnionNormalRead | Actual exposure, comparison reads, Head, Required, and forest Required retain union normality on every stopping outcome. The same successful graph returns retain it at their exact final heaps. | No closure, availability, cap, or future output invariant is required. Transport through Local Scan and class editing remains outside this module. |

The row map follows canonical normalization. It need not preserve row numbers
or be injective. The call history retains actual complete states. It does
not replay every child from one final heap or assume one fixed source
inventory for all later generated queries.

The accepted-body guard theorem uses actual field loads, the actual accepted
allocation result, operation validity, cached equality fields, and equal
arity. It identifies the full returned guard with the source conjunction.
It does not infer this identity from a scalar guard-depth observation.

## Remaining producer

The earlier Required origin producer remains complete under its explicit
initial support. Read [Required origins](notes-current-required-origins.md).
The new union-normality laws retain one of its representation invariants
through actual native and reader effects. They do not establish every
invariant needed at every outer caller.

Native recursive provenance still needs the original callback normalization
argument. A body can use its local only as a bare root or root-union member.
The actual callback filter can erase that occurrence. The raw source body
still has a live varying input, so the new raw-absence theorem does not apply
without another argument. The earlier erased-record theorem concerns later
reconstruction of the returned record. It also does not solve this original
input problem.

Complete that bridge through nested Mu and causal warm first writers.
Then compose native products, Required origins, inherited combine/descent,
and actual parent returns into progress for fresh outer-node evaluations.
The measure must respect the complete physical request key. An alternative
is a proof that the new request differs from every evaluating owner.
Ordinary height and maximum constrained depth do not provide this measure.
Do not assume a future successful graph, returned-child rank, or globally
idle node table.

Nonempty live walks, ordered rows, ordinary outer-node bodies, and full mutual
completion remain open. Repeated-pass convergence is a separate obligation.
Current frontend and error adapters, lazy forcing and publication, concrete
host effects, total memory capacity, public composition, and full Haskell
correspondence remain open.

## Evidence and Haskell handoff

Evidence is in `restart-evidence/20261017-native-row-origins/`.
Its README and checkpoint-validation.json record exact selected probes,
raw logs, source snapshots, effective resource limits, and preservation.
Full Audit passes 3051 jobs and 67320 dependency checks. The effective limits
are 4 GiB MemoryMax, 4 GiB MemoryHigh, and zero swap. Peak memory is 410 MiB.
All four final production strict logs are empty. All canonical targets pass.
Only propext, Classical.choice, and Quot.sound are permitted kernel axioms.
Earlier failed attempts and their raw evidence remain preserved.

No Haskell change or new production defect is added. Root FINDINGS keeps the
external repair registry first. Field-pool repair b9219b9e remains merged and
validated in unchanged source c0cc8a05. The original Chain example returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pools.
Every later repair must record its failure, executable reproducer, affected
paths, commit, checks, and upstream status in root FINDINGS.

All earlier proofs, counterexamples, repairs, drafts, optimized interned
code, stashes, and other worktrees remain preserved. The whole-library goal
remains active.
