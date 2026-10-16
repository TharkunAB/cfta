# Conditional native output profiles

Validated 2026-10-16 19:31 CEST. Source is frozen.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryOutputStored.lean` (208 lines).
SHA256: `0dfa1e39d10a4040025538ec8af7195a3645e02cd20c33e8d6c420f5152a6f3f`.

The node and edge certificates have the requested empty-seen condition and quantify over both original profiles. Output rows use rows squared. Output arity uses max arity 1. This includes the one-child rejection sentinel. Only returned cells carry the certificate. Other phases carry no result premise.

The twelve lifecycle theorems retain their names and argument order from the older finite ordinary Stored component. A finish requires a separately proved local certificate for its exact evaluating owner. Warm receipts derive complete request equality from physical validity and key safety before reading that owner's profile. The original Stored, ScopeCache, and NativeProfile source hashes match this checkpoint's initial snapshot.

## Validation

- Pinned direct Lean: `output-stored-direct-1.log`, exit 0, no diagnostics.
- Root canonical target: `output-stored-build-1.log`, exit 0, 1066 jobs. Its only warning is the historical dependency's unused `inputs` binder. The new module has no warning.
- Fifteen public signature and axiom pairs: `output-stored-public-2.log`, exit 0, no warnings or sorryAx. This includes both certificate definitions, Stored, and all twelve lifecycle theorems.
- Five integration signature and axiom pairs: `output-stored-kernels-3.log`, exit 0, no warnings or sorryAx.

The integration kernels check:

1. A literal node lookup/demand evaluating prefix identifies the owner, then an independently valid Empty certificate is published at the same handle. An immediate demand returns that exact Empty and the complete unchanged native state. The edge family remains unchanged.
2. Node completion followed by edge completion retains both exact returned cells and both certificates. The local sentinel profile is constructed directly and permits the zero-input-arity boundary.
3. A physical warm node hit supplies its original request's instantiated output profile, retained Stored, and actual output availability.
4. A physical warm edge hit supplies the analogous sentinel-safe profile and actual row residency.
5. A nonempty seen list imposes no profile condition on an arbitrary result.

The first two kernels test certificate installation. They do not assert that their local certificates come from a completed checked query body. That producer theorem is a separate component. Initial warm Stored is a causal certificate premise; physical validity alone does not derive it. No eager-execution transfer or future callback is used.

The initial kernel attempts failed because an evidence expression left `.empty` ambiguous, then because a FlatMemoThunk demand equality needed lifting through the full native record. Both failed raw logs remain. The final run contains five clean kernel axiom reports and no sorryAx.

No Lake process, older source edit, Haskell edit, Audit edit, or Git operation was performed by this component task. Root owns the canonical build. Existing runtime, source-adapter, and general-domain boundaries remain separate.

Packaging correction 2026-10-16 19:31 CEST: the public probe source had an extra EOF blank line. It now has one terminal newline. The exact public probe was rerun once into output-stored-public-2.log and passed with fifteen complete signature/axiom reports. Log1 remains unchanged. No proof source changed.
