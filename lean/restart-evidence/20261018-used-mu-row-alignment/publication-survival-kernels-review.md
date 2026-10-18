# Nested-used publication row-survival integration

Frozen at 2026-10-18 10:45 CEST. This component changes no production source. It contains one constructed theorem, `MicroCFTA.PublicationSurvivalKernels.nested_used_row`.

## Initial source and actual publication

The source is the raw outer binder `mu x. node0[x, raw mu y. node1[y,x], leaf2]`. The outer row has symbol zero, full guard `false`, and three ordered children. The nested row has symbol one and full guard `true`. The last child is an ordinary zero-arity row with symbol two and full guard `true`.

The fixture constructs the outer `Publication` from its three literal callbacks. The Depth callback starts at the empty source heap. The ordinary callback starts at the actual Depth return. The missing key determines the actual reservation. The reserved body callback starts at that allocated heap. The initial joint source context is the proved empty context. Each callback completion and the missing-key fact is checked from the source definitions. No writer, callback completion, child-output relation, or row schedule is supplied as a theorem input.

`Publication.build_done` gives the actual complete source result. Source construction derives `Ready` at the returned source heap. Computation proves the installed full candidate, the exact returned candidate, and `usesLocal=true` for the outer Mu. It also proves that child index one of the selected stored row is an actual nested Mu with `usesLocal=true`. The stored body and ordinary values differ. The body syntax is not `BinderFree`.

The selected row is an actual member of the stored body's physical `nodeEdges`. It has the exact source symbol, complete guard, and arity three. The source has a single root row. Thus the same source-position witness retained by `Paired` refers to that sole source row. The positive membership and nested-used witness prevent an empty-output or binder-free case from satisfying the statement.

## Applied producer and exact boundary

The fixture invokes `SourceCurrentPublicationNodeRowSurvival.publication` with the actual event, its literal node syntax, and the selected stored body row. The resulting `Paired` evidence retains both actual `buildEdges` calls and both `makeNode` outcomes. It retains the same source row index, full symbol and guard, each row's ordered child call, exact row allocation, prefix and suffix, and growth into the actual reserved-body endpoint. It proves that the selected body row has a surviving ordinary-callback row with matching full fields. The ordered child physical-empty tests agree, and both rows are alive.

The common reader in `Paired` is exactly `event.afterBody`. The separate `Ready` conclusion concerns `event.after`, after the outer publication. The fixture does not identify these heaps. It does not infer chronological source membership from a bare growth premise.

This is row-survival and schedule evidence. It does not prove equality of nonempty child records, `Related` for those children, complete callback literal alignment, or general retained-Mu reconstruction congruence. It does not include a root-union filter extension or an older warm-winner case. The nested source is active syntax; it is not merely an opaque recursive capture.

## Selected validation

- Strict selection: `publication-survival-kernels-direct-3`, terminal zero, actual zero-byte raw log.
- Strict source SHA256: `fa7f2457bee67c0ae41acec83093fdc6e603d189a7d07dd56396b402d23debfc`.
- Full selected group: `publication-survival-kernels-public-1`, one constructed pair, zero production pairs, zero auxiliary pairs.
- Full source SHA256: `af7f8bea7b3d8b7e297b76c21a01c2de327e5b0a949dded59652d72012357a2a`.
- Full output: 27324 bytes. Hardened probe validation passes all eight options, `#check @`, full public proof printing, and axiom printing. There are no warnings, errors, omissions, printer failures, or `sorryAx`. Only standard axioms occur.
- Selected checks execute pinned Lean 4.34.1 with all linters. The inner worker reads effective cgroup values `memory.max=4294967296`, `memory.high=4294967296`, and `memory.swap.max=0`. The wrapper sets a five-minute time cap.

The first attempt missed the namespace that exports `callback`. The resulting elaboration errors caused later declarations to fail. The exact owned Lean process was stopped with SIGTERM; the wrapper recorded exit 143. No memory-cap or timeout claim is made. The second attempt had one surplus tactic after `cbv` had already closed the non-BinderFree goal. It returned one. Both snapshots, raw logs, metadata, limits, and the explicit first-attempt stop record remain preserved. The final strict attempt and full probe pass.

This is an evidence-only component. It has no independent canonical production target. The production owner supplies the checked canonical source. The component manifest pins final production source bytes and owned files only. It does not pin mutable root evidence.

Final root producer SHA256: `9a394d88e00b73676b87eda6aa4849f4c9c91943970bb58a181ab0b76aac1e0a`.
