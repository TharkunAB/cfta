# Normalized source comparison and causal Mu readback

Starting checkpoint: 87a430e2a7cf238d8f178490f5be268f668db566.
Proof commit: 179b5a099a2ef01224833f871c7f78d30b884f53.
Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e, merged at `896b0a1c`.
The pre-work pull passed. Publish only formalize.

The 17 production modules have empty final strict source logs and passing
canonical builds. The full pinned Audit passes 3080 jobs and 67877 dependency
checks. Actual limits are 4 GiB MemoryMax, 4 GiB MemoryHigh, zero swap, and 399 MiB
peak memory. The only canonical replay warning is the older unused input
at InternedFreshOrdinaryClosedCompletion:24. New strict/public logs are clean.

There are 102 new public declaration checks and 9 constructed checks in 22
selected groups. Public declarations include definitions, structure fields,
and constructors. Each public declaration has a full signature, proof or
definition, and axiom report. Constructed declarations have full signatures
and axiom reports. Every selected source sets all eight required explicit
linter and printer options. Selected logs have no diagnostics, omissions,
truncation, or sorryAx. Only propext, Classical.choice, and Quot.sound occur.

The general normalized source comparison and unused stored-Mu law are now
proved. Actual finite source publication histories establish the immutable
law before each candidate write. A warm request uses its earlier selected
winner and exact current probes. The public producers accept no desired
MuHeap or future callback equality. closed_compared retains the actual two
successful raw calls, initial contexts, finite label coverage, both live
fixed-support freshness conditions, first noDeep, and actual growth and
issued histories into its closed-source common heap. It gives equality of
ordered stripped root alternatives, not literal raw record equality.

Constructed checks cover aliased varying names, discarded colliding captures,
duplicate removed references, actual filtering and warm union replay,
causal nested writer order, full warm state replay, complete outer workers
with an unrelated active owner, constrained B beside productive Mu, later
Required, an initial-source binder decomposition, and nested/union or
bare-self unused Mu cold-to-warm readback. They are evidence for those
constructions. They do not prove general outer progress or convergence.

UnionNormal retention now covers all eight bounded mutual outer workers.
Native recursive trace composition, general outer progress, repeated-pass
convergence, frontend/runtime adapters, and whole-library correspondence
remain open. The whole-library goal stays active. Read the current proof
note and general proof-status note for exact boundaries.

No Haskell patch or new production defect is added. FINDINGS keeps the
external repair registry first. Field-pool repair b9219b9e remains merged
and validated. The original Chain example returns
Left (FieldAtomOnDatatype "Next" 0). Standalone holds retains opaque pools.
The unchanged source reuses strict Nix, 798 examples plus golden, Fourmolu,
and Cabal-gild evidence. These tests do not establish missing adapters.

All failed attempts and raw snapshots are retained. Root comparison-core18
and comparison-inactive3 probes overlap the combined core21 probe; they are
unselected. The selected combined core and Execution groups use their final
public2/kernel2 variants. Earlier public1/kernel1 variants remain retained.
Those reruns added optional pp.all while preserving all required options.
Each statement is counted only once. Raw artifact whitespace is recorded;
it is not removed. CONTINUE.md retains the earlier working plan below a
final-state notice. That older plan must not restart completed work.

verify-checkpoint.py checks all final modules, strict sources, canonical
builds, selected probes, caps, Audit, and component manifests.
verify-preservation.py checks all 18029 starting files, 3062 older non-Audit Lean
sources, 242 Haskell files, 206 active-package files, 2 stashes, 3 other worktrees,
and 106 frozen module manifests with 837 hash references. The Haskell repair
registry and historical FINDINGS suffix remain intact.

SHA256SUMS covers every file in this directory except itself. Force-add all
listed raw logs because Git ignores .log by default. After commit,
verify-closure.py checks filesystem, index, HEAD, file modes, all checksums,
and reproducible retained reports. Optional remote readback also checks the
published formalize tip and unchanged main tip. Keep closure output under
/tmp to avoid checksum self-reference.
