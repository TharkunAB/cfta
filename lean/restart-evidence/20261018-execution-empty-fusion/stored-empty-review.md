# Stored Empty interpreter: scope and validation

Date: 2026-10-18 15:10 CEST.

## Result

`SourceCurrentStoredEmptyInterpreter.test` is a pure Boolean function. It
evaluates the complete `encode (leaves value) [] value` syntax using the
root profiles of the actual resolved leaf inputs. It does not interpret an
original Mu from that Mu's decoded shape alone.

Five public declarations are selected:

- `test`: the pure full-plan physical Empty test;
- `closed`: a closed value remains a literal captured profile;
- `reference`: a reference uses its optional replacement or its original reference;
- `open_mu`: an open Mu evaluates its full encoded body under a smart binder;
- `execute_test`: an actual completed repaired execution has exactly that Boolean test.

The first four declarations have no equality typeclass premise. The actual
execution theorem requires the ordinary executor's `DecidableEq EdgeKey`.
Its initial premises are `Ready`, source availability, replacement
availability, and the literal successful execution equation. It derives
the source context of the encoded leaf inputs. The existing full repaired
profile theorem supplies the returned profile. Actual normalization and
returned availability identify the physical Empty test. It does not take
an output profile, result relation, final readiness or future completion
law as an input.

## Boundary

The theorem covers arbitrary stored values, including nested active Mu
bodies. It imposes no BinderFree, no finite Cap, no closure restriction and
no absence-of-local-occurrence premise. The closed equation exposes the
actual literal shortcut. The open Mu equation retains the full original
body and lexical own-name slot. It does not replace the body by a raw
shape or remove the smart binder branch.

This is phase one of Empty fusion. It does not compare the encoded plans
of two different source callback values. In particular it does not prove
physical Empty agreement for every `RetainedMuDirectedCase.Generated`
pair. The source/filter/first-writer fusion obligation remains open.
No general execution completion or outer progress claim is made.

## Constructed integration

A private copy of the prior boundary builds one closed source from empty
tables. Its two used Mu children have exactly equal decoded shapes. One
body is `f[x,z]`. The other is `f[x] union f[z]`. Actual sequential stored
calls replace the same captured outer self `z` with Empty. The first call
returns Empty. The second returns a physically nonempty value.

The fixture invokes `execute_test` on both literal calls and proves
`test first environment = true` and `test second environment = false`.
It also invokes `closed` on the original closed source root and proves its
test is false. The source completion, initial `Ready`, input and replacement
availability, local use, exact shape equality and both sequential `Keeps`
are derived internally. The source bodies differ. This is not a Generated
counterexample and does not assert accepted finite-language inhabitation.
The public fixture is an alias with exactly the checked private witness's
explicit statement. This avoids expanding its computed proof term.

## Checks

Final production SHA-256:
`0e10a012b0773ccc5a01087ae7147e461963465dbc16bbb396e67c4657639e59`.

Selected strict production: `stored-empty-direct-2`, exit 0 and 0-byte log.
Canonical build: `stored-empty-canonical-1`, 554 jobs, no warnings.
Selected production group: `stored-empty-public-1`, five full triples.
Selected constructed strict: `stored-empty-kernels-1`, exit 0 and 0-byte log.
Selected constructed group: `stored-empty-kernels-public-1`, one full triple.
Each group includes all eight explicit print/linter options. Only
`propext`, `Classical.choice` and `Quot.sound` may occur in axiom reports.

Attempt 1 is retained. Recursive equation theorems in `simp` caused a
looping-simp warning and recursion-depth failure in the closed/reference
proofs. Attempt 2 rewrites each recursive definition once, then simplifies
only the resulting nonrecursive branch. No execution definition changed.

Every selected check uses pinned Lean 4.34.1 with a five-minute cap.
Effective MemoryMax and MemoryHigh are both 4294967296 bytes. Effective
MemorySwapMax is zero. Resource readbacks and each attempt are preserved.
