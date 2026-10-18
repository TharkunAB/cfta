# Stored profiles and causal publication induction

Checked at proof checkpoint `9a840a6c`. Starting checkpoint is `92fc8a02`.
Source main remains `c0cc8a05`. The branch is `formalize`.

## Strongest general claim

For the checked Lean constraint reducer, a successful bounded call adds no
finite tree outside the input language. It retains every input tree that satisfies the
inherited equality constraints. With inherited payload `some []`, input and
output have the same finite-tree language. This statement assumes the
initial semantic cache facts, recursive guard-profile agreement, available
inputs, and computed resource bounds. It does not prove that every returned
tree satisfies all inherited constraints.

The endpoint is `SourceCurrentOuterInitialActual.node_call`. Its language
contract is `SourceCurrentAllocatedPartialMemoSound.NodeLaw`. General
termination, semantic initialization from every public call, and full
Haskell correspondence remain open. This is a conditional correctness
result for the model, not a whole-library completion claim.

## New checked results

`SourceCurrentStoredProfileFunction.denote` interprets the full stored
substitution encoding under arbitrary reference profiles. It retains the
literal closed-value shortcut. It treats open recursive values through
their actual stored encoding. Coherent available storage makes this
function depend only on the value's actual free names. Actual completed
substitution gives an equivalent root profile under the resolved input map.

`SourceCurrentPublicationHeapInduction` retains a state-independent payload
predicate through actual issued publication paths. Each publication gets
the proved predicate for all earlier callback heaps. It must prove the
predicate for its exact candidate. The theorem covers both complete and
pending source stopping states. Closed source execution starts with an
empty payload table. The semantic publication obligation remains explicit.

`SourceCurrentStoredMuProfileContract.Correct` is a candidate payload
invariant. For every outer profile assignment and every local profile, the
stored body and ordinary probe have equivalent denotations after binding
their respective local names to that profile. `execute` transfers this
contract to actual completed body and ordinary calls. The readers and final
heaps can differ. Initial readiness, availability, and replacement validity
remain explicit. No general source publication theorem derives `Correct`.

## Remaining main step

Prove the candidate contract at every actual source publication. The old
unrestricted Fusion contracts remain refuted by the preserved artificial
cache counterexample. The old uniform smaller-raw-depth hypothesis remains
impossible at every positive bound. The actual smart-unused case still
returns depth0 from a stored candidate of depth1 whose body has depth0.

A proposed proof compares two actual source builds with the same source
shape and common fixed and varying inputs. It must retain original alias
tests and exact root-filter behavior. Input profile agreement must use
surviving normalized support. Syntactic occurrence alone includes captures
from discarded rows. Ordinary freshness does not cover every unused input.

The raw-binder case needs separate closed and open handling. Original raw
syntax is opaque in the simple source evaluator. Full stored encoding
reconstructs an open raw Mu with a smart binder. Thus source denotation
cannot simply be identified with evaluation of the original syntax.

Use strict source-body comparison to prove each publication candidate from
its earlier callback heap invariants. Then use actual publication history
induction to retain that candidate for later hits. This is a proposed proof
route. The required general binary source comparison remains unproved.
Changing-capture semantic observations and initial recursive guard-profile
agreement remain separate obligations. Completion, repeated convergence,
machine integer adequacy, Sized, enumeration, ranking, and probability
contracts remain in the full-library scope.

## Validation and preservation

The three new modules add sixteen public declarations. Their complete
statements, proofs, and axiom dependencies pass the hardened checks. Full
Audit passes 3360 jobs and 72733 dependency checks. Only the existing
ClosedCompletion unused-input warning remains. Builds use Lean4.34.1 under
a 4 GiB systemd memory cap with swap disabled.

Evidence is in `restart-evidence/20261018-causal-profile-invariant/`.
Three actual fixtures cover open nested Mu substitution, an ordinary opaque
node, ignored bound-name assignments, closed-value profiles, and causal
publication induction in the smart-unused case. An installed smart-unused
candidate has a live outer capture. Its parametric contract is derived.
Two actual sequential substitutions use a nonempty local replacement and
change that outer capture. The checked execution bridge compares their
profiles and retains the installed payload. This example does not derive
the contract for every source publication. Six selected strict logs are
empty. Five manifests pin 234 entries. The selected manifests record the
final attempts. Earlier failed and incomplete attempts remain.

No Haskell bytes change. Field-pool repair `b9219b9e` remains fixed in
`c0cc8a05`. Root FINDINGS retains the Haskell repair registry first.
The counterexample concerns an insufficient proof contract. It establishes
no actual source-history counterexample and requests no Haskell repair.
Publication still awaits direct approval after the earlier automatic review
rejection. No push is retried. The full-library goal remains active.
