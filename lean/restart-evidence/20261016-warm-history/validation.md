# Exact serial native history validation

Validated 2026-10-16, Europe/Stockholm.
Source main: `8f85ddb605327bd088aae970ab058137c4f6d762`.
Starting published proof: `3e84dab7005f315395f6335cd0be241fd6593871`.
Proof commits: `ef5bbc8e`, `2bdf6641`, `c8fe3b9f`.
Audit and scope note: `133ffb69`. Restart documents: `73954c8d`.

## Authoritative successful outputs

- `full-audit.log`: terminal 0; 2294 jobs; 56040 theorem dependency checks.
- `inventory-build-20261016.log`: terminal 0; 455 jobs.
- `inventory-public-probes-20261016.log`: terminal 0; seven public axiom
  reports, seven signatures, fourteen kernel examples.
- `memo-build.log`: terminal 0; 1088 jobs.
- `memo-probe.log`: terminal 0; seven public axiom reports, seven signatures,
  eighteen kernel examples.
- `warm-query-build-2.log`: terminal 0; 1124 jobs.
- `warm-query-probes-2.log`: terminal 0; three public axiom reports,
  three signatures, one kernel example, one named kernel theorem, and
  that theorem's axiom report.
- `history-build.log`: terminal 0; 1126 jobs.
- `history-probe.log`: terminal 0; three public axiom reports, three
  signatures, three kernel examples. The repeated-query example derives
  equal literal results and an unchanged final warm return.
- `cold-history-build-2.log`: terminal 0; 1128 jobs.
- `cold-history-probes-1.log`: terminal 0; one public axiom report,
  one signature, one kernel example, one named kernel theorem, and
  that theorem's axiom report.

Total: 21 public reports, 21 signatures, 37 kernel examples, and two named
kernel theorems. The named theorems add two reports. Only propext,
Classical.choice, and Quot.sound occur. Canonical builds repeat the existing
unused-input warning from InternedFreshOrdinaryClosedCompletion.

The public commands use the pinned toolchain:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

Focused builds use the same command with the corresponding module name.
Public probes ran from the lean directory with the same lake executable,
`env lean`, and the repository-local probe path. Raw failed intermediate
logs are retained unchanged. In particular, warm-query-probes-1.log reports
the rejected intermediate arithmetic proof and its placeholder dependency.
The corrected final probe and the full Audit pass. The failed intermediate
probe is not an imported library proof.

## Evidence of the required behavior

The finite operand inventory derives one physical representative, one
input model, and every listed root's validity and physical language.
WarmQuery derives independent actual contextual and scope completions.
It aligns their returned value and complete checked state.

WarmHistory composes the literal actual Code.walk. Whole-walk machine ranges
derive each head plan and the reached tail plan. Actual head receipts admit
the next query in the same model. Ordered laws retain exact original
intersection languages and closed resident results. Earlier completed
keys and exact returned cells survive the actual tail. Every cacheable
historical query therefore repeats in two checked steps with the entire
final checked state unchanged.

ColdHistoryExact derives the model and all operand membership from the
full finite list. Empty native tables derive Contextual, Scoped, and Idle.
Its public premises contain no initial warm cache, desired output law,
future successful body, or model-validity callback. The cold kernel theorem
derives actual stable execution, final physical and semantic invariants,
ordered independent root laws, closed available results, and final warm
repeats directly from that endpoint.

Independent read-only reviews are inventory-review.md, memo-review.md,
and history-root-review.md. No material defect was found. The reviewed
source hashes match frozen-modules.json. Initial Good, SemanticReady,
original closed available operands, and reached WordRanges remain explicit.
The history uses one fixed source inventory. New generated operands,
cross-model admission, GHC publication, concurrency, concrete storage, and
unrestricted machine capacity are not claimed.

## Preservation and source status

preservation-final.json checks the 3291-file starting manifest. No file is
missing. All 2288 older non-Audit proof sources retain identical bytes.
All six preceding frozen manifests pass. Only the seven restart documents
and additive Audit imports change among baseline files. Stashes and other
worktree records remain unchanged. Earlier unavailable external draft bytes
are not claimed recovered or reverified.

No Haskell implementation or test changes occur. The diff against main
still consists only of the historical constructor repair's changelog entry
and the equality reproducer comment. Root FINDINGS.md retains each repair's
failure, path, commit, checks, and upstream status for external work.
Reuse the strict Nix all-component build, six suites with 777 examples plus
golden, five-file Fourmolu, and four-package Cabal-gild recorded there.
Those checks were not repeated because source bytes did not change.

All owned process handles are terminal. This checkpoint is concrete progress.
The full-library goal remains active. The next proof target is initial
Good and SemanticReady from complete original allocation, normalization,
and field histories, followed by current class Scan and constrained outer
caller composition. Other full-library and distinct Sized targets remain.
