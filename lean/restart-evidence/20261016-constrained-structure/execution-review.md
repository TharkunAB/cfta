# Finite ordinary execution review

Reviewed: 2026-10-16T16:23:59+02:00.

Verdict: no material defect found in the frozen execution proof. This is a
structural theorem for completed current checked physical traces. It is not a
request completion theorem or a language theorem.

## Principal premises

`SourceCurrentAllocatedFiniteOrdinaryExecution.verified` (lines 76–84) requires
an actual completed `Trace`, initial physical `Good`, initial `SemanticReady`,
allocated continuation `Fields`, initial `Stored`, and a static
`CertifiedControl`. `Good` contains physical native validity, required-heap
readiness, valid equality operations, and loaded annotation fields. It contains
no `NodeProduced` or `EdgeProduced` result law
(`SourceCurrentAllocatedNativePhysicalCompletion.lean:28–33`). Physical native
validity uses original request readiness and returned residency only
(`SourceCurrentAllocatedNativePhysicalCache.lean:20–37`).

The generic static certificate is explicit. The public `node_trace` and
`edge_trace` wrappers derive it for literal requests (Execution lines 245–269).
They do not require an externally supplied certificate for their own output.
The wrappers still require a completed physical trace and initial warm
`Stored`. Cold empty native tables derive `Stored` without a result premise
(`SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored`, lines 97–99).

## Actual recursive calls and publication

`verified` uses strong induction on the supplied trace length (lines 85–89).
Each recursive body is extracted by literal bind inversion. Its trace is
strictly shorter because the enclosing request already consumed one step
(lines 153–169 and 214–223). The local node or edge code certificate is derived
before that recursive call. No future body completion or own result law is a
public premise.

Physical lookup/demand identifies the full captured request before compilation
(Stored lines 143–207; Execution lines 135–148 and 198–210). This retains domain,
ordered operands, and complete original edge records. Body retention preserves
the exact evaluating handle (Execution lines 171–172 and 225–226). The proof
then splits its actual finish, derives availability or residency from that
physical finish check, and installs the newly derived certificate at the same
owner (lines 173–189 and 227–243). The full checked operation state is retained
by the literal step equations. Warm hits read the certificate at the physically
identified request. They do not replay a different body or reset native tables.

Static `Certified` forbids explicit enter/read/binder/finish instructions in
this fragment (Code lines 31–48). The principal interpreter handles only the
protected finish frames that literal native request expansion creates. An
arbitrary physical trace with an arbitrary finish is therefore not silently
covered.

## Domain and both bounds

`NodeInputs` and `EdgeInputs` require empty `domain.key.seen` and the finite
ordinary operand domains (Code lines 23–29). They do not require empty domain
free names or empty guard equality classes. The domain excludes Mu, references,
and explicit unions recursively; guards remain unrestricted (Domain lines
19–37 and 94–105). A nonempty seen list is deliberately outside these request
endpoints because the earlier repeated-pair branch can return a reference.

Node row joining retains an ordered certificate for each actual pair. Each
returned edge is bounded by the left row maximum and separately by the right
row maximum. Actual `makeNode` then derives each parent bound independently
(Node lines 48–104). Reset, exact self reuse, swap, and ordinary dispatch follow
the literal decision order (lines 107–145).

The edge proof follows the literal child zip, derives each child domain and
both child bounds, and uses exact raw constructor readback (Edge lines 51–124).
Mismatch and rejected guard branches construct the singleton-Empty sentinel
(lines 126–139 and 218–239). This has zero child height even for original
nullary rows. No output arity equality is asserted. Full guards and nonempty
equality classes need no semantic truth assumption for this structural result.

## Verification and remaining scope

The final source hash is `c8d546542d20fc2005a01c364eb2c1b5c5de4849cfcdd44518dfe9faef107d57`.
The existing parent `execution-build-1.log` records terminal success at 1113
jobs with only the historical unused `inputs` warning. This review ran no
compiler or Lake command and changed no proof source.

The theorem does not construct a physical trace from arbitrary native `done`,
prove native completion, discharge machine word checks, admit arbitrary warm
result tables, derive language equality, or cover recursive binders/unions.
A finite adapter must supply or construct the actual checked trace under its
stated initial domain and range conditions. No GHC forcing, runtime key-table,
concurrency, or whole-library correctness claim follows. No source bug or
Haskell repair was found by this review.
