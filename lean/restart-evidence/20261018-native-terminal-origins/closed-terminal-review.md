# Closure at the exact native root terminal writer

## Selected source and checks

The production module is `lean/MicroCFTA/SourceCurrentNativeQueryClosedTerminal.lean`.
Its SHA-256 is `ca225df23bfd0e07ecf4b1c35f4ff2f3b5624c5742dce2958d34d4affbb7e93f`.
The selected immutable strict source is `closed-terminal-direct-4.source.lean`.
Its executed log has zero bytes and exit code zero.
`closed-terminal-canonical-1` completes with 1414 jobs.
Its only warning is the unchanged imported warning from `InternedFreshOrdinaryClosedCompletion`.

`closed-terminal-public-1` independently imports both public declarations.
It uses `#check @`, full `#print`, and `#print axioms` for each declaration.
It explicitly sets all eight required linter and printer options.
The hardened probe check passes without omissions or printer errors.
The axiom reports contain only the three standard permitted axioms.
Every selected run records effective MemoryMax and MemoryHigh of 4294967296 bytes and MemorySwapMax of zero.
The runner enforces a five-minute bound and executes immutable snapshots directly.

## Exact statements

`route_closed route leftClosed rightClosed` derives closure of both ordered terminal operands of the SAME `NativeQueryRowOrigins.Route`.
A route hop records a swap or a domain reset.
The swap exchanges the two closure facts.
The domain reset leaves both operand values unchanged.
The induction follows the actual stored request sequence retained by the route.
It does not change the route or select a different writer.

`closed_residual origin leftClosed rightClosed` opens the supplied actual `RowOrigin` witness.
It returns that same terminal request, handle, route, returned cell, and full Written witness.
It additionally returns both terminal operand closure facts.
It preserves the original self row alternative and the complete ordinary Joined alternative.
The remaining decision alternatives are exactly bothMu, leftMu, rightMu, leftUnion, and rightUnion.
Both reference alternatives are eliminated from the literal decision definition.
A bare reference always has a singleton free-name list, so it cannot be a closed terminal operand.
The decision's earlier empty, reset, self, swap, repeated-pair, and unsupported branches cannot equal either reference tag.

## Scope

The only caller inputs beyond the existing Route or RowOrigin are closure of the two initial root operands.
There is no new Good, Normal, Coherent, Available, History, BinderFree, finite Cap, desired reconstruction law, or completed future call premise.
The RowOrigin retains its existing actual checked-route and earlier writer semantics unchanged.
The new proof strengthens that exact witness; it does not construct an unrelated request or row law.

The result applies ONLY to the normalized root forwarding route.
It does not ban reference branches in recursive native requests, stored body reads, Mu callbacks, or ordinary probes.
Closed Mu and union roots can contain open internal reconstruction work.
The five remaining residual cases still require their actual exposure and reconstruction lineage producers.
No general native or outer completion theorem is claimed.

## Preserved attempts and ownership

Attempts 1 through 3 retain immutable failed sources, full raw logs, metadata, and effective resource readback.
They record a missing namespace import, unused simplifier equations, and literal decision case-splitting corrections.
Attempt 4 is the strict-clean selected source.
No source guard or decision algorithm changed.

The component manifest uses an explicit allowlist of this production file, frozen imported source definitions, and owned `closed-terminal-*` files.
It does not pin any shared selection file, root runner, root working fixture, or another component's evidence.
No constructed scenario is counted in this bounded general proof component.
