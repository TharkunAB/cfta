# Actual smart-binder reader rows

Reviewed and frozen at 2026-10-18 09:00 CEST.

Production: `lean/MicroCFTA/SourceCurrentNativeBinderReaderRows.lean`.
SHA-256: `2c0b6ba3d576edf93539b85d8d59af865f766f53dec8e1c217d844e57b29f10e`.

The public declarations are `Rows` and `binder_row`. The producer starts with an actual repaired `build (.binder true body) environment before = .done value after` and the initial joint `ConstrainedCapSourceHistory.Context before environment`. It also takes final-reader `History empty reader`, forward `Grows after reader`, and one literal physical row index in `nodeEdges value`. No publication History at before is assumed or inferred. No caller supplies a raw callback equation, completed row law, future completion, or desired row relation.

The actual binder decomposition produces both current probe callbacks, the actual request, the raw ordinary build, the literal root self-filter, and the semantic Context at every captured cut. The receipt retains these exact equations and all Contexts. It also retains availability of the current raw result.

The depth callback's verified physical effects derive before-to-afterDepth Grows and issued Extends. The raw build's verified effects derive afterDepth-to-raw Grows and issued Extends. Actual decomposition supplies raw-to-after transport. The receipt includes those three exact links and the composed before-to-raw and before-to-after links. These facts allow an earlier available stored body to be transported to the actual ordinary raw entry. They are derived execution effects, not future growth premises. Reader growth transports only the selected complete record forward; issued extension into the reader is not inferred from Grows.

The actual request supplies the complete selected record at the current depth/ordinary key, including warm older winners. The final actual Context supplies DepthHeap.Correct for that record. The physical selected row then gives usesLocal=false, value=storedBody, absence of its interned self name, and the same indexed stored-body row. The proof uses final-reader History only after transporting this exact complete record forward. The history law equates the actual value with erasure of the CURRENT ordinary callback, even if the selected record was allocated earlier.

Actual raw Context, availability, and the self-filter equation derive all-view row Origin equivalence between the actual result and current raw ordinary build. The selected complete edge is also a raw Origin at every view. Origin retains the full guard, symbol, and ordered children.

The theorem has no BinderFree, NoDeep, finite Cap, or closed-source restriction. It covers arbitrary source syntax and captures that satisfy the explicit initial joint Context. It does not construct completion from scratch. It applies to a direct physical nodeEdges selection, not an arbitrary epsilon row of a retained-used Mu. It does not identify a raw encoded source call with repaired stored execution by itself. The root specialization supplies stored plan equivalence and derives final reader History from the actual causal trace. General retained-used Mu reconstruction correspondence remains separate.

Selected receipts:

- `binder-reader-direct-1`: exit 0; actual raw log has 0 bytes; executed immutable source equals final production.
- `binder-reader-canonical-1`: exit 0; warning-free successful canonical build, 595 jobs.
- `binder-reader-public-1`: exit 0; two complete #check @, #print, and #print axioms pairs; all eight required options explicit; no omissions or printer errors; only propext, Classical.choice, and Quot.sound.

Each run uses pinned Lean 4.34.1, five-minute heavy-management limits, and inner effective cgroup readback memory.max=memory.high=4294967296 and memory.swap.max=0. Direct and public checks run immutable numbered snapshots with -Dlinter.all=true and the compiled LEAN_PATH.

The component has no failed attempts. Its counts are two public pairs and zero constructed pairs. The source-built stored-Mu specialization is root-owned. The manifest uses an explicit owned-evidence and frozen-dependency allowlist. No root working fixtures or shared mutable component files are pinned.
