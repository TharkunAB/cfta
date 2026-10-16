# Grown resident input inventory validation

The new source file is `lean/MicroCFTA/SourceCurrentAllocatedNativeGrownInventory.lean`.
It has 145 lines. Its SHA256 is
`58b1ecc566535d1296d487557f47a958b4ef883388da966c6389607caf8e2e6f`.
The source is frozen. No older proof source, Haskell file, Audit, or Git
metadata was changed by this task.

## Public contracts

All endpoints are in `MicroCFTA.SourceCurrentAllocatedNativeGrownInventory`.
They are generic in `Symbol` and `Guard`; they need no `DecidableEq` instance.

* `closed_originals target facts roots available closed` derives `Original`
  for every target root from its actual availability, closed free field,
  and the coherent target heap. No supplied target `Original` oracle is used.
* `reachable_grows source target sourceFacts targetFacts growth history holds
  roots originals available closed input reached` derives actual
  `InputInventoryModels.Reachable target holds roots input` from reachability
  in the source. A private `InputReach` induction retains both old validity
  and actual target reachability. Each constructor uses the corresponding
  field agreement. Reference closure uses the old finite interface.
* `valid_grows` additionally takes `targetRoots`, target availability and
  closedness, and literal source-root membership inclusion. It derives
  membership in the **actual target** `InputInventoryModels.finiteInput`,
  whose target syntax witnesses come from `closed_originals`.
* `rank_exact` proves an `inputAt` equivalence at the same rank for each old
  valid input, using actual source and target inventories.
* `language_exact` proves the corresponding erased-language equivalence.
* `name_rank_exact` and `name_language_exact` expose these equivalences
  directly at `identity input`, given an old-admitted nonempty input.
* `target_root_valid` admits each listed new closed resident target root
  through the actual target inventory's `root_valid` theorem.

The shared premise order after `source`, `target`, and their `Facts` is:
actual `Grows`, issued-map `Extends`, fixed `holds`, old roots,
old original/availability/closedness proofs, target roots,
target availability/closedness proofs, and old-root inclusion. The public
probe prints the full authoritative signatures.

Old and target root orders and multiplicities can differ. Only root
membership inclusion is needed. No total-view or total-language equality is
claimed at new or otherwise unadmitted identities.

## Validation

Focused command:

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeGrownInventory
```

Terminal result: **PASS, 650 jobs, exit 0, no warnings**.
Raw final log: `grown-inventory-build-2.log`.
The first log retains the repaired missing section-variable inclusion error.

Public and kernel command:

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-semantic-admission/grown-inventory-publicprobes.lean
```

Terminal result: **PASS, exit 0, no warnings**.
Raw final log: `grown-inventory-publicprobes-3.log`.
Eight public axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`. Eight full signatures are printed. Eleven kernel examples
pass. The example heap builds a leaf with the actual fresh constructor,
then builds a distinct leaf in the returned heap. The target roots are
`[new, old, new]`. The examples check actual counters `1 → 2`, distinct
identities, old and new admission, exact rank and language transport,
rank-zero acceptance before and after, and rejection of arbitrary admission
from an empty root list. Earlier failed probe logs are retained as drafts;
they are not validation evidence.

## Root growth-model source review

`SourceCurrentAllocatedNativeInputGrowthModels` was read without edits.
`derivation_exact` retains literal ranks in both directions. The reference
case obtains Mu validity before reading the retained body.
`reverse_agreement` rewrites target membership to source membership before
using closure. `lift` retains the old domain and representative. Its
`copy_exact` derives original closedness through exact free-field agreement.
No material proof or scope defect was found. This review did not run a
separate canonical build of that frozen root module.

## Remaining boundaries

The target availability and closedness of each new root are current input
conditions. Source-root inclusion is explicit. These endpoints do not prove
that a dynamic native result belongs to the old inventory.

No warm contextual cache is transported here. Captured request admission,
and agreement at captured `domain.seen` pair identities, remain necessary
for that next step. Physical cache validity alone does not supply either
semantic fact. No future native result, completed callback, final cache
validity, or semantic answer is a premise of this module.

Machine identity capacity, actual GHC publication and forcing, and the
general outer constrained caller remain separate source bridges.
