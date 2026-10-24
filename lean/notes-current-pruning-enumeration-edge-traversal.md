# Ordered native edge child traversal

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `7f16f7fb2a9737419f129c06074d1c318ce99877`.

The operation runs the same native edge prefix once. It consumes the captured
child actions in their original order. It runs each present action before the
tail. A missing action returns None at the actual current enumeration state.
Earlier rejection and errors take precedence. The worker does not check all
children for support before execution.

The concrete traversal theorem derives success from the same native inputs.
It uses coherence, child availability, closedness and nonempty children.
It uses the actual pending-slot invariant and aligned allocation supply.
The edge theorem assumes inherited arityAllows is true.
It computes the first absent captured action. The actual completed prefix
returns fresh holes in order. The full traversal reaches the same endpoint.
Its result is None at an unsupported child and Some after all children finish.
The counter increases by the number of completed children. The theorem retains
the actual endpoint, supply alignment and all pending native readbacks.
No callback-success law or chosen output-state equality is assumed.

The edge theorem derives child availability, closedness and nonemptiness
from one actual closed ordinary parent. Ready supplies coherence and live-edge normalization. Availability
supplies the actual edge children. Closed-parent metadata supplies child
closedness. Live edges exclude empty children. The theorem consumes the same
prefix result and its actual equality-allocation state.

On None, the operation retains the child endpoint without a parent residual.
On Some, it constructs the fragment from the same symbol and ordered children.
It records a present complete residual with the existing recordResidual action.
Only obligations change in that final update. Supply alignment and pending
native readbacks remain. Full compression-frame preservation is not claimed.
Projection absence remains an outer None. It differs from unsupported child
execution, list rejection and enumeration errors.

Three strict inputs failed: broad simplification reached the default limit; an implicit action witness did not elaborate; a redundant final tactic had no remaining goal. The fourth input passes with a literal empty log under all linters and warnings as errors. All failed inputs, full logs and exact corrections remain. No proof limit changed. The complete public readback, installed build and Audit pass. All 168 public-output lines retain four complete signatures without display omissions.
The installed build passes 622 jobs. Audit passes 3692 jobs and
76173 dependency checks, with the unchanged older warning.
runStaged reports no axioms. The other three declarations report exactly propext, Classical.choice and Quot.sound. No project axiom is added.

The frozen declarations, scoped types, independent reviews, all actual inputs,
full logs and resource receipts remain in the evidence package. The previous
edge-prefix checkpoint's 26 actual post-seal inputs remain. These include its
prospective assessment and its post-publication summary.

Terminal merging remains open. It needs native representative changes,
waiting-count transfer, assimilation and intersection at the actual heap.
The own-arity guard already exists. Its checked constructor receipt still
needs transport to the same selected edge and projected tries. The default
canonical and weighted selector remains separate.

Mu and retained-union children keep the existing diagnostic cutoff slots.
This does not prove complete-language nonemptiness below a cutoff.
Projection normalization remains noncomputable. Extracted execution, native
graph/ID/index/memo2 correspondence, the complete typing/pruning callbacks,
lazy driver, practical widths, runtime/solver correctness and convergence
remain open. H6 remains the strongest combined theorem. H23 and older
constructor/equality work remain. All earlier work and the optimized core
remain. No Haskell source changes. FINDINGS retains all six repair handoffs
first. The full goal stays ACTIVE and incomplete.
