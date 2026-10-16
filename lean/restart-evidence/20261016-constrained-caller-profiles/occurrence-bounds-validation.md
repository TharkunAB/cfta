# Occurrence bound validation

Date: 2026-10-16 19:51 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.lean`.
The source has 127 lines. SHA256: `8f72bb3da839b09780e2b3e1a190813a5f47841feee13f93d8d118a81eda9b7a`.
The evidence copy is byte-identical. The production source is frozen.

## Checks

- Final direct source check 2: terminal exit 0, no diagnostics. Session 22361 was polled to terminal exit 0.
- Canonical build: terminal exit 0, 396 jobs. Parent confirmed the terminal result. The raw log is `occurrence-bounds-build-1.log`.
- Imported public probes: terminal exit 0. All 10 public declarations have an axiom probe and a full signature probe.
- Final imported integration probes 3: terminal exit 0. All 3 kernels have an axiom probe and a full signature probe.
- Imported serial probes 1: terminal exit 0. All 3 public SerialCallerResources declarations and its independent capacity kernel have an axiom probe and a full signature probe.
- Final imported logs have no warnings, errors, or `sorryAx`. Axiom reports contain only standard `propext`, `Classical.choice`, and `Quot.sound` where used.

Direct source draft 1 retains two nil-case simplification failures. Kernel draft 1 retains two elaboration failures. Kernel draft 2 passed but reported an unused section instance in a private evidence helper. Final kernel 3 removes that unused instance. No production source changed after final direct source check 2.

## Results

`nodeCount R A 0 = 0` and `nodeCount R A (H + 1) = 1 + R * A * nodeCount R A H`.
`edgeCount R A 0 = 0` and `edgeCount R A (H + 1) = R * (1 + A * edgeCount R A H)`.
Both functions are monotone in height.

The mutual `node`, `rows`, `edge`, and `children` theorems bound the literal recursive occurrence counters from the initial uniform profile and height only. The forest bound multiplies each per-node bound by the exact original forest length. The proof contains no heap, worker completion, child callback, or result-law assumption. Full guards and equality classes have no added restriction. Profiles exclude Mu, union, and reference constructors.

## Kernels

1. A concrete two-row, three-child, two-layer tree repeats the same lower child identity six times. Its literal counts are 7 nodes and 14 rows. Both computed bounds are attained.
2. The general node theorem proves those concrete bounds from the original profile and height.
3. One actual Required return derives an input-only occurrence bound for the returned forest. Its output profile, length, and height are derived from the same literal return.
4. The independent serial kernel constructs Required followed by Projection at its literal returned heap. Initial headroom alone bounds both final supplies at the same two actual returns.

The independent SerialCallerResources source review found no material defect. Its reviewed source hash and scope are recorded in `occurrence-bounds-serial-review.md`.

No older source, Haskell, Audit, root document, or earlier frozen evidence file was edited. This owner ran no Git or Lake command. New owned text has one final newline and no blank line at EOF. Derived compiled objects remain outside the evidence directory.
