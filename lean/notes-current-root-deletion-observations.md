# Original root deletion and actual unused binders

Checked on 2026-10-18 at proof checkpoint `2e24eca5`.
Earlier proof commits are `f1c0441f` and `c29d794f`.
The starting checkpoint is `8de10a50`. Source main remains `c0cc8a05`.

## Checked results

`SourceCurrentStoredRootDeletion.deleted` tests original bare root
references before profile assignment. It follows original unions.
It does not delete names that a replacement or stored Mu later exposes.
Its support and uncut laws are checked.

Actual node and union normalization preserve this observation.
The union theorem uses the original inputs before flattening, duplicate
removal and ordinary-node merging. These constructor laws need Normal
and available inputs. They need no Ready or semantic payload premise.
Actual self filtering has a standalone-reference exception.
`SourceCurrentStoredRootDeletionErasure.erased_filter` proves that the
filter followed by bare-self erasure adds self to the original root cuts.
It also needs only Normal and availability.

`SourceCurrentStoredMuRootContract.Correct` is a checked sufficient
payload interface. It compares arbitrary original root cuts and local
profile replacements. It also preserves bare-reference tags.
It implies the prior profile contract and actual filtered-profile laws.
The preserved artificial cache fails this stronger contract.
Actual raw/smart and cold/warm examples derive it from empty caches.
These examples do not prove general publication preservation.

`SourceCurrentCausalPublicationHeapInduction` carries actual forward
history prefixes to each candidate callback. The callback receives the
earlier heap facts and History empty afterBody. The semantic candidate
proof remains an explicit obligation. The induction does not prove it.

`SourceCurrentNativeUnusedRootDeletion.build` exposes the actual current
ordinary callback and its strict source-body call. For a smart-unused
binder, every root deletion observation of the result equals the strict
body observation with its local name added to the cuts.
It needs a completed source call, its Context and an actual history from
empty. It needs no assumed parametric payload contract.
Four actual bodies check this endpoint for cold and warm calls.
They cover bare self, a nullary node, an external reference and a union
of self with that external reference.

`SourceCurrentNativeReaderUnusedRootDeletion.build` gives the same
reduction from a later reader. It needs Grows after reader and History
empty reader. It retains the exact selected record through forward
growth. It requires no history at the earlier source-call entry.
This is the form needed for fixed-reader source induction.

## Next substantive proof

Prove general source comparison at one fixed reader. Keep actual completed
calls, their Contexts, forward growth and issued-name extension explicit.
The reader must supply the required normal and old payload heap facts.
Use live input aliases, equal assigned profiles and aligned original cuts.
Preserve the separate bare-reference test.

The unused binder now reduces to strict source-body calls.
Use actual erased callback absence to align their local assignments.
The retained open-Mu case still needs a shared fresh marker and the prior
payload law for the exact selected record. Do not infer a bare tag from
equal assigned profiles. Do not send root cuts into a retained Mu body.

Then use the prefix-carrying publication induction to prove each actual
candidate's old payload contract before installation.
Do not assume that contract for the current candidate.
The stronger root contract remains a sufficient interface. It is not a
required premise of the proposed causal comparison route.
See the pinned causal route review and unused-reader audits in
`restart-evidence/20261018-root-deletion-observations/`.

## Verification and preservation

Ten new modules pass strict checks with empty logs and clean canonical
builds. Thirty-one public heads and seven constructed heads pass complete
statement, proof and standard-axiom checks. Full Audit passes 3378 jobs
and 72915 dependency checks. It retains only the existing unused-input
warning in InternedFreshOrdinaryClosedCompletion.
All Lean jobs use a verified 4 GiB cap with no swap.
Selection, source hashes, failed attempts, manifests and restart checks
are retained in `restart-evidence/20261018-root-deletion-observations/`.

The broad guarantee remains
`L(input) intersect Sat(inherited) <= L(result) <= L(input)`
under the stated cache, guard, input and resource assumptions.
It does not prove that all returned trees satisfy inherited constraints.
Exact returned size-query APIs have the separate enumeration, count and
rank/unrank laws in `notes-current-system-claim.md`.
General recursive initialization, completion, convergence and full
Haskell correspondence remain open. The full-library goal stays active.

No Haskell bytes change. Root FINDINGS retains every repair entry.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`.
This checkpoint adds no Haskell defect or repair request.
All work stays local. No push is retried.
