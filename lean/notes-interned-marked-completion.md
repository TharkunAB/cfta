# First-run completion from preserved binder root markers

`InternedMarkedCompletion.closed_completes` proves that a marked nested
expression completes from empty tables. `closed_not_pending` excludes
every incomplete canonical readback. Neither theorem assumes that the
first execution succeeds or that its callback keys are stable.

`Tagged` checks the condition on the original expression. Each binder body
is an ordinary node with at least one declared nullary edge. All outgoing
edges of that body have one marker symbol. A nested binder uses a marker
different from every enclosing binder's marker. Other child expressions
can use nodes, unions, empty branches, and arbitrary nested smart or raw
binders. Siblings can reuse a marker after earlier requests complete.

`InternedNestedRootLabels` derives the source signatures of every completed
edge. `makeNode_root` proves that the nullary edge survives empty-child
removal and canonical sorting. Complete cache readback retains the exact
edge payloads. The resulting ordinary node therefore exposes its declared
root marker. Source self-union normalization leaves that root unchanged.

Each active `Frame` contains its actual depth and ordinary probes. Its key
is the source pair of probe references. `Context` retains derived record
facts, available lexical inputs, residency of active depth probes, and
`Covered` for exactly the active frame keys. It does not contain a
noncollision assumption.

`request_not_pending` proves the key distinction. An incomplete table
entry must name an active frame. Equal keys would give equal resident depth
probes. Their complete root labels would then agree, which contradicts the
source declaration's marker restriction. The recursive completion proof
adds one frame at reservation and uses successful coverage preservation to
remove that permission after completion.

`closed_complete_record` combines first-run completion with the full nested
provenance and replay proofs. It supplies `Facts`, `Covered []`, an
`Available` result, and exact replay after arbitrary later table growth.
The examples include fresh enclosing references, empty branches, unions,
and two siblings that reuse the same marker. `examples_scoped` checks that
their lexical variables are bound.

This is a sufficient source fragment. It does not prove first-run
completion for arbitrary binders with overlapping root markers or bodies
that normalize from a union or another binder. Use `Scoped 0` when reading
the executor expression as closed source syntax. The generic constructor
model receives already prepared edge guards; these theorems do not add a
proof that an arbitrary rejected `mkEdge` guard preserves a marker. The
examples use ordinary unconstrained edges.

Pinned Lean 4.34.1 builds `MicroCFTA.InternedMarkedExamples` in 152 jobs.
The isolated dependency audit permits only the three standard foundation
axioms. No Haskell implementation or committed test changed.
