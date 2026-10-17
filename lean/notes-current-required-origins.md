# Current Required origins and remaining outer progress

Starting published checkpoint: e4b949a5.
Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Whole-library target

For every public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Specify intended behavior first. Then prove correspondence with current
Haskell. Support must describe initial inputs and resources. It must not
assume a future successful worker, graph, or returned result. Errors and
validation order form part of the contract. Exact accepted terms, counts
by size, enumeration order, both rank/unrank inverses, transformation
relations, generation, and sampling remain separate obligations.
The earlier component map is in notes-current-outer-progress.md.

## Checked structural origins

| Module | Result | Boundary |
| --- | --- | --- |
| RequiredExposureSafe | Empty requirements retain arbitrary inputs. Ordinary requirements inspect only selected existing child slots. Recursive exposure requires the actual plain predicate. | This is an initial local domain, not a progress measure. |
| RequiredUnionNormal | Actual construction, stored execution, and unfolding retain irreducible union records. A stored union has no all-ordinary merge. Full syntax includes smart and raw nested Mu, warm winners, and pending outcomes. | Other heap fields remain separate. Coherent or SemanticReady alone does not include this invariant. |
| RequiredFiniteExposure | A closed available depth-zero record satisfies every Needed requirement under semantic readiness and derived union normalization. | Ordinary guards remain unrestricted. No plain-guard premise is needed. |
| RequiredRowOrigins | Actual Required node, child, and row execution retain indexed original rows and ordered child origins. Nonplain and positive physical equality rows project to original structural occurrences with the same full guard, symbol, and arity. | Ordinary normalization can remove or reorder rows. The map is not injective and does not preserve row numbers. |
| RequiredPrimaryExposure | Actual false primary traces derive the local structural domain at a retained caller. Compiled and selected path unions keep their exact signed lookups. | The caller retains its own semantic, available, and union-normality facts. Secondary false traces alone are insufficient. |
| RequiredPrimaryOrigins | Initial caller facts construct complete Required execution with ordered origins and its exact guarded-language receipt. Actual closed construction derives readiness, costs, guard observations, and union normalization for the source entry. Initial operand availability and the earlier false primary class remain explicit. | The false primary class is an earlier branch certificate. No future Required result, graph, or origin law is an input. This does not complete outer recursion. |
| NativeCallbackErasure | Actual normalized callback output with no deep local occurrence loses its free local name after bare-self erasure. Any two replacements then give identical complete stored-reconstruction outcomes, including nested Mu and warm branches. Actual native callbacks have the same law. | The theorem concerns subsequent reconstruction of the returned callback record. It does not exchange the original callback inputs or equate a stored warm body with its ordinary probe. |

The structural address includes an ordinary row index and child index,
a union member index, or a stored semantic Mu-body step. It excludes both
Mu probes. Identity origins preserve arbitrary uninspected subtrees.
Accepted recursive regions have only plain rows, so they supply no
nonplain output occurrence. Other ordinary guards can be nonplain.

The finite shortcut needs a causal representation fact. SemanticReady
contains flat unions, nonempty members, and coherent metadata. It does not
state that an ordinary-only union was merged. Actual makeUnion derives
that additional fact. The new source induction retains it through every
constructor and first-writer readback. This avoids an unsupported inference
from readiness alone. It is not a new Haskell defect.

## Remaining general progress obligation

Required origins now have an actual primary producer and a completed
source entry. General native row provenance remains to compose through
ordinary products, unions, Mu callbacks, and earlier warm winners. The
callback erasure theorem supplies a local reconstruction law. It does not
yet give the complete body-to-probe row relation needed by that producer.

Then relate actual parent returns and inherited combine/descent to fresh
node evaluations. Unequal-length edits can copy constrained values deeper.
Native products can stack constrained levels from both operands. Ordinary
height and maximum constrained depth are not decreasing measures.

The resulting measure must respect the actual complete request keys.
Historical labels alone cannot exclude a busy physical memo cell. Ready
hits require no fresh body descent. Evaluating ancestor owners require a
separate disjointness or compatible well-founded decrease argument.
The existing key-identity, busy-owner, and edge-idle results remain valid.
Read notes-current-outer-owners.md for their exact domains.

After that producer, complete nonempty live child walks, ordered rows,
ordinary node bodies, and the full mutual pass. Repeated-pass convergence
remains separate. Current frontend and error adapters, lazy forcing, memo
publication, concrete host events, resource capacity, public pipeline
composition, and full Haskell correspondence remain open.
Do not add a future returned-child rank, successful graph, or globally
idle node-table premise to replace these obligations.

## Evidence and Haskell handoff

Evidence is in restart-evidence/20261017-node-origins/.
Read its README and checkpoint-validation.json for final canonical,
strict, public, constructed, dependency, and preservation checks.
Only standard kernel axioms are permitted. Failed and superseded attempts
retain their source and raw logs. Unchecked drafts are not proof results.

A finite Haskell search checked 3651 constructed cases. Every instrumented
result matched current reducePartially by physical Node equality. No
active-key recurrence was found. Eight selected cases also passed in fresh
processes. Those are a subset, not additional distinct cases. The actual
outer node cache was cold, but the earlier instrumented traversal had
already populated native and parent caches. The copied instrumentation
is not a verified Haskell trace. This is search evidence, not general
progress or source correspondence.

No Haskell behavior change or new production defect is added.
Field-pool repair b9219b9e is already merged in unchanged source c0cc8a05.
The original Chain example returns Left (FieldAtomOnDatatype "Next" 0).
Standalone holds retains opaque-pool evaluation. Root FINDINGS keeps the
external repair registry first. Every later repair must record its failure,
executable reproducer, affected paths, commit, checks, and upstream status.

All earlier proofs, counterexamples, repairs, marked drafts, optimized
interned code, stashes, and other worktrees remain preserved.
The whole-library goal stays active.
