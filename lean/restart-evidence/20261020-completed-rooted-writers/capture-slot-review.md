# Indexed original capture prototype review

Frozen on 2026-10-20 at 15:26 CEST. All sources, runs, and evidence are under `/tmp/mcfta-source-capture-original-slots`. No repository or official evidence file was edited. The generic module and constructed fixture are separate.

The generic candidate `SourceCurrentSourceCaptureOriginalSlots.lean` has exactly two public heads in `MicroCFTA.SourceCurrentSourceCaptureOriginalSlots`:

- `original_slot path slot captured found row inside` returns an original index with `slot = crossings.length + originalSlot` and `initial[originalSlot]? = some captured`.
- `empty_initial path slot captured found row` excludes `RowAt captured row` when that supplied path starts with empty original inputs.

The proof uses the existing exact `Path.inputs` equality. Indexed recursion removes one literal callback reference at a time. A lookup in that prefix would identify the captured value with a literal reference, which has no `RowAt` constructor. The surviving lookup retains the original suffix index. The proof never weakens lookup to set membership.

The laws allow arbitrary original values and structural rows below arbitrary nested Mu or union records. They require no BinderFree, capacity, closedness, reader availability, semantic output law, or desired origin premise. Their source-path premise remains explicit. They do not produce a rooted path for a completed resident writer; that is a separate causal source producer. They do not assert empty native encoded capture lists. An encoded stored execution can capture closed leaves and actual external replacements.

The separate fixture `capture-slot-kernels.lean` begins with the exact generic source bytes, then adds `MicroCFTA.SourceCaptureOriginalSlotsKernels.actual_callback`. This arrangement permits a check before the generic module is installed. The fixture source-builds an ordinary leaf, derives its actual semantic source context and availability, then enters the Depth callback of `binder false (var 1)` with that leaf captured. The actual callback returns the leaf at the same heap. Its rooted Path has one crossing, and the row-bearing value is at lexical slot one. `original_slot` derives the exact original singleton lookup and offset. Arithmetic in the returned equation forces original slot zero; no source-index uniqueness theorem is claimed.

Selected strict attempts `capture-slot-generic-direct-1` and `capture-slot-kernels-direct-1` both have exit 0 and literal zero-byte logs. Selected full groups are `capture-slot-generic-public-1` (two generic declarations) and `capture-slot-kernels-public-1` (one constructed declaration). Both have exit 0, all eight printer/linter options, full statement/proof/axiom commands, no warnings or omissions, and only standard allowed axioms. The original combined strict/full runs remain unchanged and unselected after the requested source split. Six terminal jobs are retained. There are no failures and no live jobs.

Every job records fresh usage above one percent and effective max/high 4294967296, swap zero, and a five-minute timeout. The mutable peaks file is excluded. Its immutable final six-row snapshot is included. Receipt commands retain their actual `/tmp` execution paths.

The manifest uses explicit HERE and ROOT roles. HERE entries resolve beside the manifest after any basename-preserving copy. ROOT entries identify the two established imported source modules. The verifier derives repository ROOT as `HERE.parents[2]` after installation, or takes it as an explicit first argument for checking in `/tmp`. No destination checkpoint name is assumed. The generic candidate has no dependency on another new prototype. No Lean job is run by the verifier.
