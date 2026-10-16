# Supporting outer resource checkpoint

Starting formalize: dcf12dc3b9366e5d503336960e5dfeed696964d9.
Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e.
The bounded SSH pull completed without a source or formalize update.
Local backup: backup/formalize-before-outer-resources-20261016-2208.
Proof commits: 32d29695, 2328161d, and d4cb078f.

The three new modules retain actual raw reconstruction resources, strong
lower profile stores through Target/Force/Leaf reads, and source equality
normalization/payload/precheck bounds. The current note records each contract:
`lean/notes-current-outer-resource-components.md`.

Passing validation:

- RawRebuildResources: canonical 1251 jobs; four public pairs; two integration pairs.
- LowerProfiles: canonical 1315 jobs; five public pairs; three integration pairs.
- ConstraintEnvelope: canonical 1075 jobs; 17 public pairs; seven integration pairs.
- Full Audit: 2624 jobs and 60653 theorem dependency checks.
- Public and integration probes: 38 clean axiom/full explicit signature pairs.
- Component manifests: 164 entries verified, including four historical inputs.
- Preservation: 7913 starting files; 2620 older non-Audit proofs; all 234
  Haskell files; 49 frozen production manifests with 381 module entries;
  stashes and three other worktrees.

Only propext, Classical.choice, and Quot.sound occur in passing probes.
No diagnostic or signature truncation appears in the final passing probe logs.
Failed direct/kernel attempts and their source snapshots remain separate.
The early checkpoint verifier drafts are preserved. The final verifier handles
explicit universe levels on axiom names, accepts the declared printing budget,
and checks exact historical read inputs. None of these changes weakens final
production hash verification.

Run `python3 lean/restart-evidence/20261016-constrained-outer-resources/verify-checkpoint.py`.
Run `python3 lean/restart-evidence/20261016-constrained-outer-resources/verify-preservation.py --require-current`.
Both scripts write reports in this directory. Copy them to a new evidence
directory before adapting or rerunning them during a later checkpoint.

`frozen-modules.json` checks all three final production sources directly.
`historical-snapshots.json` resolves one exact concurrent ConstraintEnvelope
draft read in the supplementary lower-chain source list. Its exact bytes are
`constraint-envelope-direct-5.source.lean`. LowerProfiles does not import that
module. Three further references resolve the starting restart documents from
published dcf12dc3. The read-only outer design recorded those earlier inputs.
The final documents have an explicit allowed preservation change. No frozen
manifest or older proof is rewritten to make a checksum pass.

Whole outer capacity remains open. Next prove strong store retention through
the remaining actual edit/class/pass/local/parent chain and all eight outer
families. Derive hereditary generated-guard bounds and causal warm output
certificates. Compose the actual height recurrence and initial headroom, then
discharge the reached-parent Plan. Guard normalization can extend paths.
The checked source step and completed normalization retain a length-three path
from inputs whose maximum path length is two. The parent live branch processes
ordered own records only. Neither observation is a Haskell defect.

General recursive progress, repeated-pass convergence, current frontend and
runtime correspondence, and full public pipelines remain open. Constructor
request bounds do not count equality allocation, solver work, or total runtime.
The full-library goal stays active.

No Haskell source changed. No new Haskell defect was found. Root FINDINGS keeps
the external repair registry first. Recursive field-pool repair b9219b9e is
merged by PR #65; the retained Chain reproducer returns FieldAtomOnDatatype.
Reuse unchanged strict Nix validation: 798 examples plus golden, six-file
Fourmolu, and four-package Cabal-gild and metadata checks.
