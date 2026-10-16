# Initial resources for the current Scan class stage

Frozen: 2026-10-16 21:47 CEST.
Owned source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryStageResources.lean`.
Source SHA256: `1e220513f5342d47e35c88ce41a858272fc28133e11fe0250295edf26e3f13e8` (185 lines).

## Public interface

outputRows and outputArity alias the PassResources output profile functions. nodeBudget adds C times the initial per-node ordinary occurrence bound to the computed pass node budget. edgeBudget uses the corresponding edge occurrence bound. These functions inspect only the initial class records and initial R/A/C/D/H envelope.

complete takes formula and solver models, initial inventory, width bits, admission budget, original records and forest, full Checked state, fourth memo, Merge memo, initial Ready and At, available inputs, proper nonroot class paths, coherent ascending active record fields, initial fourth correctness, physical Merge validity, Merge profile certificates, native and output certificates, CacheCovers, initial global validity, uniform input profile/length/path-depth/height bounds, and cumulative constructor headroom.

It returns its own raw Reduction with literal outcome none and the literal same fourth memo. The return includes its own strict Reads, existing full stage Receipt, nine-bound StableRun of LocalWorker.classes, native/output/Merge profile certificates, pass output forest profile, ordered NodeNarrow, exact forest length, height bound, actual constructor Work trace, request-count bounds, final Capacity, and both final supply bounds. No StageCapacity, range plan, completed stage, desired result law, intermediate profile, or future readiness is a public input.

## Construction and same-state review

FiniteOrdinaryScan.construct derives the exact selected-only raw Scan and strict primary receipts. The selected class list is the original record path list. Scan uses no secondary gate, seeded query, or fourth-memo decision. It retains the exact full Checked state and unchanged global bundle.

Retained.records comes from the actual Scan. Its sublist property and exact selected map length prove that all original records are retained, including their order and multiplicity. The proof does not infer record equality merely from equal path labels.

CallerResources.required constructs its own literal Required return for the exact selected paths. A positive chosen stable bound supplies the actual done equation. RequiredActual.verified derives the full physical receipt for that same return. requireAll_memos derives the actual indexed global Reads and final validity for that equation. There is no supplied final global invariant.

The actual Required Work trace is bounded by literal original occurrences. The initial profile, length C, and height H bound those occurrences by C times the per-node count. Required retains R/A, forest length, and height. Native/output tables are unchanged during its physical advancement. Physical Merge validity grows through the actual effects. Profile Merge certificates remain on the same Merge memo.

Initial cumulative headroom and the actual Required supply bounds derive the complete pass's headroom at the exact Required heap. PassResources.complete starts at advanceHeap before heap with the actual Required values, derived current Ready/At, actual Required global bundle, current stored invariants, and retained input profile. The pass captures this returned forest at each class entry.

The stage raw graph joins the exact Scan, chosen Required done, and constructed pass. Its strict Reads join those exact three operational stages. ScanClassPassActual.verified derives the same full stage receipt using only internally derived finite ordinary Scan checks. Work appends Required before Pass at the exact common heap. Counter bounds follow these actual traces. The fourth memo is literally unchanged in the raw graph and returned theorem type.

The result's outcome none records the Scan result. It does not mean that the returned forest has no Empty values. Required, leaf intersections, and final propagation can narrow the forest to Empty. Independent receipt language remains conditional on satisfaction of every original class.

## Validation

- Direct draft 1: terminal exit 1. Only two local Record.paths accessor references failed to resolve. Its exact source and raw log remain retained.
- Direct check 2: terminal exit 0 with no warnings. All path accessors use the fully qualified source record field.
- Root canonical mkedge-stage-resources-build-1.log: terminal exit 0, 1568 jobs. Both new targets built; only the historical inputs dependency warning appears.
- Five imported public axiom/full-signature pairs: terminal exit 0, 678 lines. Four aliases/definitions use no axioms. complete uses only propext, Classical.choice, and Quot.sound. No warning, error, sorryAx, or truncated term appears.
- Two imported integration axiom/full-signature pairs: final direct check 3 exits 0, 811 lines, no warnings/errors/sorryAx/truncation. Earlier failing and warning-only drafts and their exact sources remain retained.
- No Lake or Git command ran under this task. No older proof or Haskell source changed. The temporary direct-check olean is removed after canonical import checks.

## Integration checks

stage_then_scan constructs the full stage from initial headroom. The actual returned receipt and produced profile then construct another strict allocation-free Scan on that same returned forest, full Checked state, fourth memo, and final global bundle. No second range, result, profile, capacity, or completion premise is required.

empty_forest accepts an arbitrary proper coherent active record list. With literal forest [] and C=0, both computed stage budgets are zero. Initial Capacity alone therefore constructs the full stage, its own StableRun, strict Reads, full receipt, stored certificates, empty result, actual Work trace with zero node and edge requests, and final supplies no greater than the initial supplies. The kernel does not assert that every worker phase fuel can be zero.

## Scope

The result covers the finite ordinary class stage with unrestricted full guards and nonempty own classes under the explicit initial record facts. It excludes Mu, references, and explicit union throughout the input profile. It accounts for actual constructor Work requests and constructor supplies. It does not bound equality-interner resources, all host instructions, GHC demand or IntMap forcing, repeated outer passes, or general recursive input completion. No new Haskell behavior defect is claimed.
