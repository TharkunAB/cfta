# Initial gate and seeded query resource checkpoint

Starting checkpoint: 50abb08b.
Backup: codex/backup-initial-scan-20261017-1243.
Proof commits: 9468af32 and c36639a1.
Source main: c0cc8a05. Local source merge: 896b0a1c.

Ten additive modules construct initial primary and secondary gate returns,
causal guard retention, supported first-seeded queries, and full caller
state. The same returns retain forecast Fits, Frame, actual reads, and
stable computed worker results. The caller retains Post and the exact
outer node table, edge table, fourth memo, and Merge table. Selected
PathSupport and pure initial SeededReserved remain explicit. Whole-forest
closure and finite input Caps are not required for these new endpoints.

Read lean/notes-current-initial-gates-seeded.md for the whole-library target,
proof map, exact support, and next obligations. Numeric conjunction
Decision/Memo resources, complete Scan composition, the full source control
flow, remaining Required caps, outer descent, arbitrary constrained Mu,
convergence, current adapters, capacity, and full Haskell correspondence
remain open. Logical majorants do not give extracted runtime budgets.

## Validation

The pinned toolchain is Lean 4.34.1. Every final strict command uses
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean and runs the
absolute immutable source snapshot with -Dlinter.all=true. All ten final
strict logs are empty. All ten corresponding canonical targets pass.
Audit passes 2971 jobs and 65537 dependency checks. Its only warning comes
from unchanged InternedFreshOrdinaryClosedCompletion.

Ten groups contain 97 complete signature and axiom pairs. They cover all
87 distinct public declarations and ten constructed integrations. Every
source enables full explicit declaration and proof printing. Only
propext, Classical.choice, and Quot.sound occur in successful probes.
Eight component manifests retain 299 entries and 299 hash references.
checkpoint-validation.json records exact sources, logs, counts, and hashes.

Final strict attempts are query-frame1, primary-resources3,
primary-numeric4, secondary2, seeded-forecast3, seeded-projection6,
seeded-numeric7, gate-guard1, gate-frame3, and seeded-caller2.
current-strict-logs.json records exact filenames and matching source hashes.
build-logs.json records only the final successful canonical targets and
Audit. Earlier failed or warning-bearing attempts retain their bytes.
They are not successful proof evidence. In particular, gate-frame-direct-2
and seeded-caller-direct-1 passed elaboration but produced warnings.
Their final replacements have zero-byte logs.

Constructed integrations cover cold allocation, exact intermediate heaps,
warm reuse, the primary endpoint/interior distinction, selected open
WarmHead projection, empty seeded queries, and native queries on closed
constrained Mu operands outside every finite Cap. The full caller kernel
derives its own initial Context, Frame, and Fits from source construction.
It selects two paths beside an unselected open depth reference. It retains
Post, language Includes, closed result, exact tables, and independent
three-fuel replay. Its pure initial reservation remains a premise. The
gate-chain kernel constructs both returns and feeds the actual first
Frame and Fits into the second call. Its fixed reaches predicate is false;
it does not establish that predicate for the complete source caller.

Run these verifiers from the repository root:

```
python3 lean/restart-evidence/20261017-initial-scan-resources/primary-verify.py
python3 lean/restart-evidence/20261017-initial-scan-resources/secondary-verify.py
python3 lean/restart-evidence/20261017-initial-scan-resources/seeded-verify.py
python3 lean/restart-evidence/20261017-initial-scan-resources/query-frame-verify.py
python3 lean/restart-evidence/20261017-initial-scan-resources/caller-resources-verify.py
python3 lean/restart-evidence/20261017-initial-scan-resources/adapter-verify.py
python3 lean/restart-evidence/20261017-initial-scan-resources/guard-scan-final-verify.py
python3 lean/restart-evidence/20261017-initial-scan-resources/verify-checkpoint.py
python3 lean/restart-evidence/20261017-initial-scan-resources/verify-preservation.py --require-current
python3 lean/restart-evidence/20261017-initial-scan-resources/verify-closure.py
```

The final review verifier also checks the original guard-scan registry.
Both review registries retain their original hashes. SHA256SUMS freezes
every file in this directory except itself. Later closure and remote
identity reports go to /tmp and do not change frozen evidence.

## Preservation and Haskell handoff

Preservation retains 15137 starting files and all 2960 older non-Audit
sources. Audit adds only ten listed imports. All 94 frozen module manifests
retain 728 entries. All 239 Haskell files and 206 active-package files
retain their starting bytes. Both stashes and three other worktrees remain
unchanged. Earlier proofs, counterexamples, repairs, marked drafts, raw
logs, and the optimized interned core remain preserved.

upstream-refresh.log records a terminal-zero fast-forward-only refresh.
No Haskell patch or new behavior defect is added. FINDINGS keeps the
external repair registry first. Recursive field-pool repair b9219b9e is
merged and validated in unchanged source c0cc8a05. The Chain reproducer
returns Left (FieldAtomOnDatatype "Next" 0). Standalone holds still treats
the supplied pool as opaque. Reuse the unchanged strict Nix build,
798 examples plus golden, Fourmolu, and Cabal-gild checks recorded in the
drawn-fields-local-worker evidence. Record each later Haskell repair in
FINDINGS with its failure, executable reproducer, affected paths, commit,
checks, and upstream status.
