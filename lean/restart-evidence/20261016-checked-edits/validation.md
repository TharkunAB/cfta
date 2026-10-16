# Checked structural edits and complete class-pass validation

Source main remains `8f85ddb605327bd088aae970ab058137c4f6d762`.
Starting published checkpoint: `b992e324be76faf82b9c8261e6e959da07fdf6e8`.
Opening git pull reported Already up to date. A later remote read confirms
the same source main. The proof commits are `63310da4`, `251fa392`,
`1e54e3cb`, `9cdb80c5`, and `7f00cf8e`.

No Haskell implementation or test file changes. The existing differences
from main remain the historical constructor changelog entry and the comment
that names OuterCallerCycle. The first registry in root FINDINGS.md describes
both. The new mkEdge entry distinction is a proof obligation, not a reproduced
Haskell defect. Each later Haskell fix must record its failure case, affected
files, commit, checks, and upstream status in that registry.

## Pinned checks

All commands use Lean v4.34.1. Full canonical command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

Terminal status 0. `full-audit.log` records 2358 jobs and 56817 theorem
dependency checks. The audit rejects placeholders, native evaluation axioms,
and project-specific axioms. Only propext, Classical.choice, and Quot.sound
are permitted. The only final warning is the older unused `inputs` binder
in InternedFreshOrdinaryClosedCompletion.

All nine new modules pass focused canonical builds. Root Complete passed
on its first attempt, 1289 jobs. Root ClassPass passed on its first attempt,
1295 jobs. Two later ClassPass builds remove unused section-instance warnings;
the final frozen source has no new warning. Failed local elaboration and probe
logs remain unchanged. They do not replace the final successful logs.

| Component | Public axiom reports | Public signatures | Integration kernels |
| --- | ---: | ---: | ---: |
| Graph and Ranges | 1 | 9 | 3 |
| Effects | 7 | 8 | 8 |
| Complete | 3 | 3 | 5 |
| Language | 4 | 4 | 5 |
| ClassEditPlan | 9 | 10 | 2 |
| ClassEdits | 3 | 7 | 3 |
| ClassPass | 5 | 5 | 10 |
| RequiredClassPass | 5 | 6 | 3 |
| Total | 37 | 52 | 39 |

Additional named kernel axiom reports and signatures remain in their raw
component logs. Independent Complete, ClassPass, and RequiredClassPass reviews
found no material defect. Exact reviewed hashes are retained.

Kernels check actual child arity for raw setChildren, constructor retention
of both native tables and operations, ignored root callbacks without native
ranges, selected leaf construction, recursive head then body with the same
global bundle, and an edited ordinary child beside an open sibling. The
two-class kernel derives distinct successive inventories and passes the exact
tail-returned forest, checked state, and warm merge table into the next class.
Other kernels derive required-to-pass execution, class-satisfying original
membership without an assumed required filter, fourth correctness, and the
next generated query from the actual full pass return.

## Preservation

`verify-preservation.py` checks all 3948 starting tracked files. None is
missing. Only seven restart documents and additive Audit imports change among
those files. All 2348 older non-Audit proof sources retain identical bytes.
Seventeen frozen module manifests pass. Stashes, other worktree records,
and the complete first Haskell fix registry remain unchanged.

Earlier unavailable external drafts and temporary snapshots remain unavailable.
No recovery or reverification of those bytes is claimed. No compiled proof
artifact is included. `component-manifest-checks.json` verifies eight component
manifests. Final SHA256SUMS covers all checkpoint evidence except itself.

Unchanged Haskell source reuses the strict Nix all-component build, 777 existing
examples plus the hole-fit golden check, five-file Fourmolu, and four-package
Cabal-gild at the PR #55 refresh. The original raw logs remain in
`20261016-physical/`. No source test is added or changed.

## Exact scope and next step

Finite endpoints construct actual completed sequential edit and class graphs.
Their annotated leaf and head receipts are conclusions of finite completion.
The final finite endpoints do not assume a successful edit or pass, a future
Ready, a generated-input model, admission, or a result-language law. Selected
domain assumptions allow unrelated ordinary siblings to remain open.

The class pass preserves every original term that satisfies all selected
classes and narrows the input language. It does not assert unconditional class
satisfaction of every output. RequiredClassPass derives the selected domains
and removes a redundant required-filter premise under class satisfaction.
It starts at an actual Required receipt; it does not construct the earlier
Scan, allocated precheck, or original construction. Initial global validity
and the range plan are at the actual required return. The preceding checked
RequiredGlobalMemos endpoint supplies that validity separately.

Next connect actual allocated entry and Scan to this pass, then the literal
parent mkEdge branch and inherited descent. Source mkEdge can reject a raw
contradiction without forcing the reduced child list. FieldAvailable alone
does not prove constructor acceptance. Later inherited descent reads the
returned edge and combines inherited constraints first. Final same-arity
setChildren is separate. `checked-outer-entry-next.md` records exact source
locations and remaining obligations.

General constrained outer completion, literal source worker transfer, GHC and
IntMap demand order, pending publication, concurrent forcing, pure selection's
noConstraint CAF allocation, concrete containers and identity, machine capacity,
solver IO, random draws, callbacks, codecs, broader frontend and recursive
generator adapters, and separate Sized contracts remain active. The full goal
is incomplete. No board message, deployment, or main-branch push was made.
