# Actual optional binder meaning: refreshed evidence

Validation time: 2026-10-16 04:47 CEST.
Current HEAD: `b09f4ebbcd333cc2203aa66c8261f787c24bc4f7`.
Owned new module: `lean/MicroCFTA/SourceCurrentAllocatedNativeMuMeaning.lean`.
Source SHA256: `c8f228087e9e4b745b779f424c57356fcca40051fef51e34e72932bdad479a3e`.
Source length: 220 lines.

## Result

The actual completed `SourceRecursiveIntersectionMaybeMu.maybeMu` supplies a least-language equation and its own-language unfolding equation. Soundness tests this transformer at the fixed original pair language and derives the fresh sound context with `PairContexts.sound_extend`.

`optionalBinder_complete_of_descent` uses strong induction on the original combined rank. At each step it derives the returned value's lower-rank candidate containment from that induction hypothesis. It then derives the extended `CompletePairs` context and uses the local body completeness component followed by the actual unfolding equation. No parent-result language law or candidate-containment law is supplied to this theorem.

`unfolded` unfolds only Mu input tags. `unfolded_language` derives its input-language equation from independent `InputMeaning`. `mu_pair_descent` derives strict sum-rank descent for both-Mu, left-Mu, and right-Mu from independent `RankedInput.body`. The two `optionalBinder_mu_*` wrappers state the original operands' soundness and bounded completeness conclusions.

## Explicit remaining premises

The constructor call must have actually completed. Its initial semantic/probe heap and body availability remain explicit. Body soundness and completeness are local component assumptions. An actual checked trace induction must discharge those assumptions, including cache hits and checked rejected-child skipping. General checked request meaning, contextual warm-cache admissibility, and unconditional checked completion do not follow from this module alone. There is no old-worker execution equality, whole-output language oracle, heap equivalence, or runtime/GHC claim.

## Commands and results

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeMuMeaning
```

PASS exit 0, 1059 jobs. Only the existing dependency unused-input warning remains. Log: `mu-meaning-build-refresh-20261016.log`.

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/mu-meaning-public-probes-refresh-20261016.lean
```

PASS exit 0. All 9 public theorem axiom reports, 9 signature checks, and 8 fresh kernel checks pass. No warning. Maximum axioms: `propext`, `Classical.choice`, `Quot.sound`. No custom axiom or `sorryAx` occurs. The kernel checks include a finite actual fresh self-pair constructor call with empty least language, the exact unused branch, actual unfolding, all three Mu rank descent cases, and impossibility at combined rank zero.

The committed PairContexts interface was rechecked after evidence loss: 18 public axiom reports and 18 signatures pass. Its separate refresh probe and log are in this directory. No missing old kernel file was reconstructed.

## Evidence loss and scope

After the environment refresh, all prior owned `/tmp` probes, logs, frozen copies, and findings were absent. No old draft was recovered or reconstructed. These are fresh checks against the surviving repository sources. Four source snapshots retain the owned MuMeaning module and the frozen PairContexts, Running, and RequestBounds dependencies. Source snapshots have the `.txt` suffix and do not add proof modules.

Only the new MuMeaning source and new files in this evidence directory were written in this task. No older proof, Audit, repository documentation, Haskell, Git, or sibling file was edited. Other new sibling files belong to the parent and other agents.
