# Original-source branching profile review

Reviewed: 2026-10-17 06:18 CEST.

The module derives initial source branching limits. The proof does not assume a completed native query, a generated-result profile, or a future supply bound. The source module is `lean/MicroCFTA/SourceRecursiveIntersectionSourceProfile.lean`. Its final SHA256 is `8222f95c88388aae6cc47957f8f482f8da6fd17db224d8f5a76bb47876af0943`.

`nodePayloads` reads the actual issued node keys below the initial node counter. `edgePayloads` reads the independent issued edge keys below the initial edge counter. Both lists omit unsuccessful reads. `limits` sums literal ordinary row counts, explicit union member counts, and actual edge child counts. Aliased issued keys can count one payload more than once. This makes the bounds conservative. No distinct-payload premise is needed.

`node_mem` and `edge_mem` use the appropriate `Cache.Valid` issued-counter law. `resident_read` uses the actual coherent canonical edge entry. `available` covers Empty, reference, ordinary node, explicit union, and Mu values. Empty and reference have no literal rows or union members. Each other available constructor has its own exact issued payload read. `child` and `body` retain the same source limits through actual availability, including the two stored Mu probes. `node_scope` and `edge_scope` apply these bounds to the existing fixed-source request scope.

`read_current` and `edge_read_current` require successful earlier reads, record growth, and the corresponding issued-key history. A later successful read at the same identity must return that exact earlier payload. The result retains the initial limits and size bound. `binding_read` uses the actual original-binding readback before it applies the source bounds. Membership in a numeric identity range alone supplies no payload witness.

`nodeSize` and `edgeSize` are additional noncomputable logical `sizeOf` sums. Their public APIs explicitly receive `SizeOf Symbol` and `SizeOf Guard`. This keeps abstract and concrete uses consistent. They bound complete stored payload syntax, including Mu body and probe fields. They are separate from the executable row/member/arity limits. They do not bound allocation requests or query runtime. An unrecorded reference has no stored-payload size claim.

The first concrete imported check found that the earlier draft fixed the default generic `SizeOf` instances. Concrete Nat/Bool instances then did not match its size conclusions. The final source makes these instances explicit. The exact earlier source remains in `source-profile-before-size-instances.source.lean` with SHA256 `4c7e764a3f07b2f6ed33bbda8cd321d6d99015779baa56a16eec131d5f2425f2`. All earlier logs and source snapshots remain unchanged.

## Validation

The final absolute-path strict source check is `source-profile-direct-6.log`. It exited 0 with zero output bytes. The final canonical log is copied to `source-profile-canonical-final.log`; the build completed successfully with 1174 jobs. Its replayed dependency warning is outside the new source.

`source-profile-public-2.log` checks 32 explicit declaration/signature pairs. This count includes the Limits type, constructor, and three projections. `source-profile-kernels-2.log` checks two integration pairs. Both final imported logs have no warning, error, truncation, or `sorryAx`. Their only axiom dependencies are the standard `propext`, `Classical.choice`, and `Quot.sound` set.

The first kernel constructs its own closed source from Empty. The source contains a recursive Mu and a two-member explicit union. The actual source has seven issued node identities and six issued edge identities. Its computed limits are rows 6, members 2, and arity 5. The kernel then runs an actual new edge and node constructor. Every earlier successful node and edge payload read retains its exact value, initial branching bounds, and caller-instance syntax bound. The Mu body and both probes satisfy the same initial profile.

The second kernel checks a real pending canonical entry with no payload. This entry contributes no node payload and no rows. It also constructs a new ordinary node from Empty and proves that an identity with no earlier payload can acquire a row count above the old source bound. This tests why successful earlier read witnesses are required. The pending-key example is a model boundary check. It is not a claim about a Haskell failure.

## Remaining boundary

The profile is local to the fixed initial source. It does not bound generated output rows, the size of a later generated binder callback, total native calls, full constructor reservations, or signed host packing. A later query that uses a generated result as an operand needs a new source profile or a produced output-profile theorem. Full mixed recursive initial resource admission still needs that quantitative execution argument. No new Haskell behavior defect was found in this component.
