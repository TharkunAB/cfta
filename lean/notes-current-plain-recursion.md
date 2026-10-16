# Finite current plain recursion and constructed root execution

Source main is `c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e`.
It was merged at `896b0a1cb36c58531ee24c5b4edfff0e935111c6`.
This checkpoint starts at published `8f063c09`.
Evidence is in `lean/restart-evidence/20261016-plain-recursion/`.

## Full objective and new result

The objective remains implementation correspondence for the whole library.
It includes accepted languages, transformation contracts, exact size
classes, finite execution, counts, enumeration order, both rank/unrank
inverses, and probability laws. Frontends, runtime behavior, and complete
public pipeline composition remain in scope. Preserve the optimized
interned core and all older constructor and equality work.

`SourceCurrentAllocatedPartialPlainNode.finite` now constructs finite
literal node execution in the plain Region. It derives the smaller-call
induction internally. No successful execution, future graph, range plan,
result law, or recursive completion callback is a public premise.

`SourceCurrentAllocatedPartialPlainRoot.constructed_root` composes this
result with covered original construction. It derives stable execution,
the same actual graph, strict Reads, reached Checks, full Post, result
availability, Stored after, and full guarded-language equivalence.
`prepared_root` also derives the ordered field allocation history and
retains its actual preparation Receipt. Neither endpoint assumes worker
success or worker range checks. Construction success and Region remain
explicit. General constrained completion remains open.

## Exact domain and initial facts

Region is `SourceEqualityPartialPlainRegion.Region`. It stops at Mu and
explicit union values. Every traversed ordinary row has empty physical
own readback and Region children. The own accessor includes positive
guard extraction. Empty stored equality payload alone is insufficient.
The input need not be a closed whole forest. Opaque terminal inputs are
not traversed. A directly traversed reference has no Region constructor.

The public node theorem takes Context, inherited Ready, available input,
Region, ReturnedDomain.Stored, and ActiveAbove the request rank.
Inherited constraints may be any ready allocated value. Stored describes
the three-way child Shape of each actual returned edge owner. It remains
separate from Context.stored, which describes the merge memo.

The constructed root derives Context, Stored, and active order from its
actual cold caller. Empty inherited allocation uses the retained interner's
canonical identity. It does not assume identity zero. This logical cold
entry is not a proof of GHC initialization, shared warm tables, or CAF
forcing.

## Proof construction

- `39a2925a` defines NodeResult and the strictly smaller-rank Below interface.
- `99296e30` derives exact inherited-prefix and indexed-descent state facts.
- `57d517ce` constructs Empty, union, and Mu terminal bodies.
- `c2c3f694` constructs child walks from smaller node calls.
- `99de70a4` constructs returned-edge descendants and ordered source rows.
- `06d7a970` discharges Below with strong induction on node rank.
- `00abe685` constructs finite exact root execution after construction and
  after actual field preparation.

Node rank is `2 * ordinaryHeight + 1`. Edge rank is
`2 * (edgeHeight + 1)`. For a running ordinary node of rank R, all its
source edges have rank below R. The row and child helpers retain one
ActiveAbove (R - 1) bound across every prefix. Independent edge completion
uses the corresponding smaller bound. Its returned Shape supplies child
Regions and node ranks below R. Completed edge and node frames restore
the original bound before the suffix.

Each child uses the literal descended payload and caller. Each row runs
its edge call, then that returned edge's descendants, then the suffix.
Reads and Checks are built for those same graphs. Only then does the
existing PartialActual theorem derive the semantic receipt. This use of
completed-graph correctness does not assume execution existence.

Warm starts retain their actual captured owners. Coherent resident values
identify the owner value with the candidate value. This transfers Region
and rank. Actual forward frames retain the selected evaluating node cell
until finish. Reverse active frames restore ancestor bounds after completed
prefixes. Both directions are required. CallSteps.node_finish derives the
exact same-handle finish from the actual body graph.

Strong induction proves Below at every rank. A candidate below that rank
uses the induction hypothesis at its own smaller rank. The step theorem
then constructs that candidate's call. Thus the public finite theorem
discharges every helper callback. StableRun supplies ten sufficient bounds
and success at every larger bound, with the same complete returned caller.

Mu reconstruction derives its actual result from initial filtered probes.
Its cleanup can remove an unused binder. The proof does not assert Region
of every returned node. Terminal bodies succeed at every execution bound,
including zero. One-pass completion does not prove a repeated-pass domain
or convergence theorem.

## Remaining work

The plain Region is an intermediate domain. General nonempty own equality
classes need their actual finite range checks and a progress argument
that survives class edits, intersections, and constraint migration.
The plain original/erased/sentinel Shape does not cover those edits.
Read `next-general-review.md` in this evidence directory before choosing
the next measure. The first stage is constrained finite ordinary input:
prove actual native domain closure and height no greater than each
operand, with structural certificates for actual warm producers. Then
compose class edits and a generalized parent certificate. General Mu
constraint migration remains separate. Do not assume a finite inventory of future recursive
keys, a successful future body, or the desired semantic answer.

Unequal-length path classes and repeated-pass convergence remain open.
Current frontend adapters, concrete host containers and interning,
machine conversions, GHC demand and publication, solver and random-source
assumptions, callbacks, codecs, and full-pipeline correspondence remain.
The older general root theorem remains conditional on successful execution.
The new Region endpoints remove that premise only in their stated domain.

## Validation and preservation

The pinned full Audit passes 2492 jobs and 58889 dependency checks.
Only the permitted foundations and the existing unused-input warning
remain. Independent final-source review and imported axiom/signature and
integration probes accompany the canonical builds.

All 5730 starting tracked files remain. All 2484 older non-Audit proof
sources retain their bytes. Thirty-two frozen module manifests check
249 entries. Historical repairs, stashes, and three other worktrees remain.
Historical draft reviews retain their exact source snapshots. They do not
replace final-source review or canonical build evidence.

This checkpoint changes no Haskell file. Reuse the strict Nix build,
798 examples plus golden, six-file Fourmolu, and four-package Cabal-gild
and metadata checks for unchanged source `c0cc8a05`. Root FINDINGS.md
keeps the external Haskell repair handoff first. Record each later repair
there with its failure, executable reproducer, affected paths, commit,
checks, and upstream status. The full-library objective remains active.
