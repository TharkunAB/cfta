# Checked target and leaf checkpoint validation

Source main remains `8f85ddb605327bd088aae970ab058137c4f6d762`.
Starting published checkpoint: `8df6baa28c83aaa025e613e6683e6d58faae9286`.
Opening `git pull --ff-only` reported Already up to date.
Proof commits: `49ae70ae`, `5f547424`, and `94a5c1b1`.

No Haskell implementation or test file changes. The outstanding source-tree
differences from main are the existing historical constructor changelog entry
and the existing OuterCallerCycle reproducer comment. Both remain described
in the first registry in root FINDINGS.md. No new behavior repair is claimed.
The registry requires a failure case, affected files, commit, checks, and
upstream status for every later Haskell fix.

## Pinned validation

All commands use Lean v4.34.1. The canonical full command is:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

Terminal status 0. `full-audit.log` records 2349 jobs and 56708 theorem
dependency checks. The audit rejects project axioms, placeholders, and
native evaluation axioms. Only propext, Classical.choice, and Quot.sound
are permitted. The sole warning is the older unused `inputs` binder in
InternedFreshOrdinaryClosedCompletion. No old proof source was changed.

Focused canonical builds pass for all seven new modules. The root Leaf build
passes on its first attempt with 1283 jobs. Every supplied execution receipt
is checked at the same actual returned value and full checked state.

| Component | Public axiom reports | Public signatures | Integration kernels |
| --- | ---: | ---: | ---: |
| TargetQuery | 4 | 4 | 8 |
| TargetGraph | 6 | 6 | 7 |
| TargetComplete | 5 | 5 | 7 |
| ClassTarget | 3 | 4 | 3 |
| SharedTargetState | 7 | 7 | 7 |
| SharedTargetForce | 6 | 11 | 3 |
| SharedTargetLeaf | 3 | 3 | 7 |
| Total | 34 | 40 | 42 |

Nine named kernels have additional axiom and signature checks. Direct probes
pass with only permitted foundations. Independent target and Force/Leaf
reviews found no material defect. Their exact reviewed source hashes are
retained. Component validation files explain each kernel and each remaining
source boundary. Failed local elaboration logs remain as evidence.

The strongest kernels compose actual generated queries twice, derive both
entry heaps and next-root equations, construct required-to-force execution,
reuse the exact returned slot without a second range plan, and retain old
slots through a generated leaf query. They supply no future result law,
completed callback, next-model validity, or admission oracle.

## Preservation

`verify-preservation.py` compares all 3864 starting tracked files. No file
is missing. Only the seven restart documents and additive Audit imports
change among those files. All 2341 older non-Audit proof sources retain
identical bytes. Sixteen frozen module manifests pass. Stashes, other
worktree records, and the first Haskell fix registry remain unchanged.

The nineteen previously unavailable external drafts and older temporary
snapshots remain unavailable. This checkpoint does not claim recovery or
reverification of their bytes. No compiled proof artifact is committed.
`component-manifest-checks.json` records seven verified component manifests.
The final SHA256SUMS covers every checkpoint evidence file except itself.

Unchanged-source validation reuses the strict Nix all-component build,
777 existing examples plus the hole-fit golden check, five-file Fourmolu,
and four-package Cabal-gild from the PR #55 source refresh. No source test
is added or changed. The earlier logs remain in `20261016-physical/`.

## Scope

The target fold, historical class slots, Force, and Leaf now use the current
checked native machine and live equality operations. The structural edit,
compiled class, right-folded class pass, final empty propagation, and general
constrained outer caller remain open. `checked-class-edit-next.md` gives the
next exact source port. Same-length source setChildren uses raw internEdge.
Positional edits preserve the child count and can use that actual branch.

This is a completed sequential graph checkpoint. Pure selection's literal
noConstraint CAF allocation, GHC forcing and pending publication, runtime
containers, host identity and comparison, machine capacity, solver IO,
random draws, callbacks, codecs, broader frontends, runtime recursive
families, and separate Sized contracts retain their stated boundaries.
The full library goal remains active. A passing audit is component evidence.

The shared board was searched read-only for cfta, lean, and formalization.
Its matching thread `b4e17bb7-f021-446d-8e6f-9a3ded53eced` has twelve older
posts, latest 2026-10-12. It supplied no newer target-fold solution.
No board message, subscription, deployment, or main-branch push was made.
