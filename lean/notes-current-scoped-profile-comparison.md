# Scoped input profiles and actual binder readback

Checked at proof checkpoint `d2c57674`. Starting checkpoint is `f74c0aec`.
Source main remains `c0cc8a05`. The branch is `formalize`.

## Current result

An actual completed binder now has a pure profile formula through its
current ordinary probe. The selected payload can come from an earlier
writer. The formula covers raw and smart finish, deep local use and unused
locals, closed and open retained Mu values, and bare-self cleanup. It
requires the new parametric body/probe contract in the final heap.
General source execution does not yet establish that heap invariant.

The strongest broad result remains conditional finite-tree preservation
for successful checked-model constraint reduction. The result adds no
finite tree outside the input language. It retains every input tree that
satisfies inherited equality constraints. With inherited payload `some []`,
the finite-tree languages are equal. Initial semantic cache facts, recursive
guard-profile agreement, and computed resource bounds remain explicit.
The theorem does not prove that all returned trees satisfy all constraints.
General termination and full Haskell correspondence remain open.

## Checked components

- `SourceCurrentStoredProfilePlan` preserves pure encoded profiles across
  independent capture contexts and local scopes. It supports arbitrary
  assigned profiles, not only profiles realized by an execution environment.
  Recapture and rebinding retain nested Mu and the closed-value shortcut.
- `SourceCurrentScopedProfileInputs` compares assignments on surviving
  normalized source support. Variable, live node-child, union, Depth,
  ordinary-probe, and reserved-body extensions are checked. Aliases and
  scoped local self tests remain separate structural conditions.
- `SourceCurrentStoredProfileComposition` gives literal node and union
  decomposition. Actual node normalization preserves the future live-row
  decision. Actual union flattening, deduplication, and ordinary merging
  preserve assigned profiles up to reference-set equivalence.
- `SourceCurrentStoredMuUnusedProfile.smart_unused` covers both unused
  body return and bare-self cleanup. It assigns Empty to the ordinary local.
  The actual depth invariant excludes the remaining retained-Mu branch.
  This theorem requires no marker and no execution premise.
- `SourceCurrentStoredMuProfileReduction` gives the exact pure open-Mu
  identity. A marker absent from the finite original assigned body leaves
  is removed from the strict body's root profile. The parametric contract
  replaces that body by its ordinary probe. No future result is required.
- `SourceCurrentStoredMuFinishProfile` composes all finish branches. Its
  complete theorem derives the finite marker from original input profiles.
- `SourceCurrentNativeBinderProfile.build_profile` connects the formula to
  literal completed source execution. Actual calls supply the current probes,
  final selected payload, depth invariant, and exact return. The final
  parametric payload heap invariant remains explicit.

The exact earlier artificial cache counterexample fails the new parametric
contract. The preserved old negative proof remains unchanged. This rejects
the inadequate cache under the new proposed invariant. It does not establish
that every actual source publication satisfies that invariant.

## Next main proof

Prove filtered comparison for two actual builds of the same source body
from compatible symbolic inputs. Use surviving support, original aliases,
scoped self tests, actual normalization, and prior parametric payload heaps.
The new node and union laws supply constructor composition. The new binder
consumer supplies the exact selected writer's ordinary-probe formula.

Retain exact root-filter control. Equivalent raw assigned profiles alone
do not identify a bare original self reference. Use the existing bare-tag
and filtered-union retention laws. Do not assume freshness for unused
captures or captures from discarded rows. Do not identify arbitrary raw
source evaluation with stored reconstruction: an open raw Mu is rebuilt
through a smart encoded binder, while a closed Mu remains literal.

Then apply filtered source comparison to the strict body callbacks at each
actual publication. Prove its candidate contract from the earlier callback
heaps. Existing issued-publication induction can then retain that contract
for later hits. This general comparison and publication step remain open.
The refuted unrestricted Fusion and uniform raw-depth hypotheses remain
refuted. Do not reuse them as attainable induction assumptions.

Changing-capture semantic observations and the initial recursive guard
profile certificate remain separate obligations. The full-library scope
still includes recursive completion, repeated convergence, machine integer
adequacy, Sized, exact enumeration, both rank inverses, probability, and the
older constructor and equality targets. This checkpoint does not narrow it.

## Validation and preservation

Full Audit passes 3367 jobs and 72814 dependency checks. The seven new modules
have 25 public declarations. Six additional checked heads cover actual
integrations and exact rejection of the old artificial cache. All selected
statements, proofs, and standard axiom dependencies are printed completely.
Thirteen selected strict logs are empty. Seven canonical builds are clean.
Audit retains only its existing ClosedCompletion unused-input warning.
Seven manifests pin 413 entries.

Actual fixtures cover unused ordinary-marker collisions, discarded source
rows, nested open raw Mu with visible outer references, closed opaque
captures, future-empty node normalization, union merging, and raw/smart
bare/used cold and warm calls. Their selected cache contracts are derived.
The nested open-Mu fixture has unused selected locals. General used-local
behavior is covered by the conditional finish theorem; the actual native
used-local fixture retains a closed Mu.

Evidence is in `restart-evidence/20261018-scoped-profile-comparison/`.
Earlier failed, warning-bearing, and incomplete attempts remain. An initial
full counterexample exclusion print ended with SIGTERM and no output. The
selected exact statement uses a named checked proof. Its strict and full
standard-axiom checks pass. No cause for the earlier SIGTERM is asserted.
All Lean runs use Lean4.34.1 under a 4 GiB systemd memory cap with no swap.

No Haskell bytes change. Field-pool repair `b9219b9e` remains fixed in
`c0cc8a05`. Root FINDINGS retains the repair registry first. No new executable
defect or Haskell repair is claimed. Publication still awaits the existing
direct approval after automatic review rejected the earlier push attempts.
No push is retried. The full-library goal remains active.
