# Original root filtering and source comparison

The root-filter proof checkpoint is `9ed6c398`.
The starting checkpoint is `c642e553`. Source main remains `c0cc8a05`.
The branch is `formalize`. The full-library goal remains active.

## Checked root-filter result

`SourceCurrentStoredFilteredProfile` interprets original root filtering
before it assigns profiles. A root union loses its selected bare reference
members. A standalone reference remains present. A root Mu remains an
original atom for the filter, even if its stored interpretation later
exposes a reference.

The function has exact original free-name support. An absent filter name
leaves the assigned profile unchanged. Actual filtering from a Ready state
has an equivalent assigned profile. The Ready premise applies at the
original filter entry. A later Ready state does not supply it backwards.
This result does not yet supply the proposed Context-only source law.

## Current obstruction

A checked local witness has two actual source-built values A and B.
They have equivalent assigned profiles for every assignment.
Their actual original root filters give different assigned profiles.
Therefore equality of all substitution profiles alone does not preserve
original root filtering.

The example uses A = union[x, node7[x,z], rawMu(z)] and
B = rawMu(union[x,z,node7[x,z]]), with distinct external references x,z.
Assign x a visible reference and z Empty. The original filter removes
bare x from A. It leaves B unchanged because B has a Mu root.
The first filtered assigned profile is Empty. The second contains the
visible reference. The original stored substitution theorem remains valid.
The failed step would move original filtering through that comparison.

The compact artificial cache witness also satisfies Context and Ready.
Its selected Mu is available. Its original profile, free-name and depth
summaries hold. Every resident Mu satisfies the newer parametric body/probe
contract. An external original root filter still distinguishes the selected
body from its ordinary probe. The summary and parametric facts therefore
do not determine that additional filtering observation.

This is a proof-contract obstruction. It does not establish a failure in
actual source publication history or an executable Haskell defect.
The full proposed same-source, two-history comparison law is not claimed
refuted by these witnesses. Its additional premises must still be checked
before such a claim can be made.
The prior unrestricted Fusion counterexample remains preserved and refuted.
The previous parametric payload consumer remains a checked conditional
theorem. Its general source publication proof remains open.

## Next proof step

The cache contract must retain original direct root-reference alternatives
for external names as well as the binder local. Testing only the already
filtered own reference can leave the old contract unchanged.

The independent design review proposes unconditional deletion observations
of original root references, with local and external labels and exact
standalone-reference parity. An equivalent representation records those
original root-reference labels and the assigned profiles of the remaining
root alternatives. It must retain local and external alias tests before
concrete name substitution. This is a proposed design, not a proved general
invariant.

Prove its node and union composition. Then prove its binder clause from
actual earlier selected writers and strict source callbacks. Each real
publication must derive the candidate property. The issued-history heap
induction only retains a property after that semantic step is proved.
Do not assume the missing publication law as an initial fact.
The Context-only source theorem also needs constructor profile laws under
its own premises. The current actual constructor endpoints require Ready.
Prove the weaker-premise laws or derive Ready at each original entry.
Do not import that extra premise without a proof.

Warm filtering of a parent union does not imply warm filtering of each
proper member. A source induction must run the finite member filters into
a later common reader, retain its heap contract, and replay those calls.
The pure assigned denotation is independent of that reader.

General recursive source comparison, semantic public initialization,
recursive guard certification, completion, convergence, and Haskell
correspondence remain open. See `notes-current-system-claim.md` for the
strongest broad reduction and constructed size-query claims.

## Validation and preservation

The new module has six public declarations. Its selected strict log is
empty. Its canonical build has no warning. Complete public statements,
proofs, and axiom dependencies use only the standard Lean foundations.
Full Audit passes 3368 jobs and 72824 dependency checks. Its only warning
is the existing unused `inputs` warning in ClosedCompletion.
Two constructed witness heads also pass complete statement, proof and
standard-axiom checks. Their combined selected strict log is empty.
They cover actual source-built noncongruence and the full artificial cache
with Context, Ready and the parametric contract for every resident Mu.

Evidence is in `restart-evidence/20261018-filtered-source-comparison/`.
Failed attempts remain with their original logs and sources.
All Lean runs use Lean4.34.1 under a 4 GiB systemd cap with no swap.

No Haskell bytes change. Root FINDINGS retains the repair registry first.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`.
No new Haskell repair is requested. Publication still awaits the existing
direct approval after automatic review rejected the earlier push attempts.
No push is retried.
