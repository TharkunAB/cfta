# Original assignment meaning and rendering across actual resource histories

Source checkpoint: 87f6dee2580ba6b668775a34325b015ff2bfe4d0.
Published base: 70c7e72aeda50b3500322250d04ee214aeccd382.
Imported main: 8766699b594eaad80381af2eee034c378ccf3192.
The whole-system goal stays ACTIVE. Keep the optimized interned core.
Preserve every older constructor and equality proof, draft, counterexample
and repair. Previous checkpoint: `notes-current-opaque-finalizer-attachment.md`.

## Goal and current strongest statements

The target is source-connected correctness for the whole CFTA system.
It includes exact finite-tree language preservation, enumeration soundness
and coverage under explicit solver, selector and pruning contracts.
It also includes correspondence with the physical Haskell implementation.
This checkpoint does not complete that target.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, remains the
strongest global exact finite-tree construction theorem. Covered closed
construction, a valid original guard-allocation history and empty inherited
payload derive width and work fuels for every finite budget and round count.
Actual modeled node calls complete. The final node stays available and accepts
exactly the original finite trees in every ambient environment. H6 does not
prove convergence or physical Haskell execution correctness.

The new strongest recursive result covers a complete recorded execution path.
Start with the actual original input Packet and initial Canonical cache.
Supply the actual ResourceHistory with projected child arity recorded at each
ordinary head. Require its supplied next decision to be the actual restart
decision. Suppose the path's own output is structurally Discharged, its actual
native render succeeds, and every residual returned by that render checks.
For an original stored pending root and its original native lookup, the actual
rendered term belongs to that original native value and satisfies all original
suspended constraints at the root. The proof constructs a full assignment.
The assignment satisfies the original input, the output's own cache and the
actual rendered state. The actual compression Frame is retained.
No desired original acceptance or final Satisfies is an input.

This is conditional whole-history soundness. The old finite producer still
returns unannotated ResourceHistory. Deriving the numeric arity decoration
for every such actual path from checked construction and intersection origins
is the main remaining semantic gap. Initial Canonical is explicit. Output
discharge, actual render and residual checks remain explicit. No theorem here
asserts that all outputs discharge or that rendering always succeeds.

## What changed

1. CompletedHeadReceipt.freshArity_of_checked_build derives the entire projected
   fresh-arity gate from an actual earlier checked-build receipt, its heap
   equation, the actual native Post and matching selected edge identity.
   Checked projected arity supplies the original resident edge. Post.keeps
   retains it. Coherent native edge identity equates it with the actual head
   edge. Packet alone does not supply checked construction provenance.
2. completed_head_output_retained derives the entire old child-retention gate
   from an actual completed head, false callback, the same remaining admitted
   ResourceHistory and Discharged at that output's own cache. A node child is
   immediate. A terminal bucket is immediate. Nonterminal Mu or Union loses
   discharge by the earlier opaque boundary theorem. Genuine closed operands
   exclude references. The actual completed child trace excludes empty input.
   No fresh-arity, Canonical or Satisfies premise is needed for this derivation.
3. narrowed_receipt_sound_of_invocation_checked_output keeps the entire old
   selected-step conclusion and all unrelated inputs. It derives both former
   local gates from checked provenance and same-output discharge, then calls
   the old semantic consumer once. Its original-inventory enteredPacket premise
   remains explicit. It is not the direct consumer of every actual history.
4. OrdinaryHistoryArityReceipt contains the entire old ordinary receipt plus
   one projected numeric arity gate. ResourceHistoryWithArity contains the
   entire old history structure with that decorated ordinary receipt.
   Their forget maps retain the exact old endpoints and bounds. Removing only
   the extra arity clause and names recovers the complete old contracts.
5. ResourceHistoryWithArity.sound proves backward assignment meaning by
   induction over that actual path. Stop and done retain the original state.
   A parked step contradicts own-output discharge by its actual retained marker.
   An ordinary step derives narrowed and callback Canonical from real receipts,
   applies the tail induction at the actual framed callback cache, derives
   retention from same-output discharge and restores narrowed satisfaction.
   Actual prefix semantics then restores original input satisfaction.
   The lower consumer uses the actual post-prefix inventory and full Memos.
6. ResourceHistory.output_packet derives a Packet at the output's own caller
   and cache by induction over the original unannotated history. The actual
   renderer uses that Packet's Safe and Stratified facts. Its render_assignment
   theorem constructs the output assignment and retains the actual Frame and
   rendered-state satisfaction. No separate final resource or safety premise
   is added. ResourceHistoryWithArity.render_sound composes this construction
   with backward meaning and the original root lookup to obtain acceptance.
7. run_finite_complete_resources_render_sound calls the original canonical
   finite producer once. It keeps the entire old admission and result first:
   one bound and actual stable outcome, OutcomeResources, actual histories for
   each bound+extra/output, and Canonical for each own output cache. It appends
   a conditional acceptance observer at the same bound+extra and actual output.
   The arity-certified history is an antecedent of that observer. It is not a
   new admission for the original producer. The old 2,235-byte header recovers
   byte exactly. The bare producer does not yet derive the added certificate.

The history carries numeric arity only as the new annotation. It does not
carry a desired per-step semantic implication, a universal Ranges predicate,
a final satisfying assignment or future success. All actual head, callback,
tail, native caller, cache, full Memos, metadata and restart endpoints stay
explicit. A boundary from one sibling is not transferred to another sibling.

## Verification and retained unsuccessful attempts

Seven modules have 892 lines, ten public theorems and two data declarations.
All seven installed sources pass -DwarningAsError=true -Dlinter.all=true.
The aggregate Audit passes 4160 build jobs and 79503 theorem dependency
checks. Its strict standalone check also passes. Public readback prints all
thirteen theorem signatures and axiom sets without elision. The ten new ones
use only propext, Classical.choice and Quot.sound. Both new data declarations
are printed. H6 and the two prior captured renderer signatures and axiom sets
match the preceding checkpoint byte exactly. Their source files are unchanged.
All heavy jobs run serially with memory.max/high 4 GiB and swap.max 0.
The aggregate replay still reports the prior unused-variable warning in
InternedFreshOrdinaryClosedCompletion. No changed source suppresses a linter.
No sorry, admit, custom axiom, native_decide or heartbeat override is added.

Preserved unsuccessful attempts remain evidence, not proof results. The first
ResourceHistoryMeaning draft lacked the local Fragment notation and failed
strict checking. The corrected version adds only that notation and passes.
An earlier rendering helper used OutputResources directly. It passed but stays
historical TEMP only. The final helper derives its Packet from ResourceHistory.
The next rendering draft failed to infer the final metadata type. The final
version adds an explicit Metadata Typing binder and passes. Root then corrected
an install-order mistake: the first combined build had run before the rendering
module was installed. Its missing-file failure and correction are retained.
The later combined build and all final strict checks pass. Both finite wrapper
versions pass; their difference is module documentation only. No failed version
is installed or counted as a successful check.

The new portable archive is
`restart-evidence/20261027-history-boundary-exclusion`.
Its verifier checks exact installed source identities, retained literal review
cuts, every sealed review payload, compressed originals and document inverses.
It also checks the exact committed archive when called with --committed.
The TEMP work area is `/tmp/mcfta-history-boundary-exclusion-20261027`.
Freeze it and the archive after all reviews and validation. Save later commit
and publication receipts outside that frozen area. Do not change any preceding
frozen area or archive. See ROOT-RESUME.json and the archived helpers.

## Next work and exact boundaries

1. Derive every OrdinaryHistoryArityReceipt from actual checked constructor or
   intersection provenance through native heap Posts. The local checked-build
   theorem is available. The full finite producer does not retain enough such
   origin evidence yet. Carry actual origin data, not a desired semantic law.
   Keep the entire old finite producer admission and stable result. Avoid
   universal Ranges or unrelated heap-wide arity assumptions.
2. Use that derived decoration to remove the arity-history antecedent from the
   finite acceptance observer. Keep actual own-output discharge, native render,
   checked residuals and the original root lookup explicit. Do not infer arity
   from normalized guard annotations or replace exact full Memos by queries.
3. Prove enumeration coverage separately under exact solver, selector, pruning
   and recursive-bound contracts. Operational stability and soundness do not
   imply coverage. Do not claim convergence or all-output discharge.
4. Close remaining API and physical Haskell correspondence gaps. Keep the
   optimized interned core and all older constructor and equality targets.
   The direct-parent/member-set union-find representation boundary remains.
   Keep focused native regressions and all external repair instructions.
5. Pull before new work. Re-read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md.
   Use the established serial 4 GiB heavy workflow. Push only the authorized
   formalize destination without force. The whole-system goal remains ACTIVE.

## Haskell and upstream

No Haskell source or Cabal file changed. Native checks were not repeated for
these Lean-only changes. FINDINGS retains all earlier repairs and reproducers.
The LPO fix, extraction documentation repair and earlier Specftacular changes
remain integrated. Main remains 8766699b594eaad80381af2eee034c378ccf3192 at the
upstream refresh. The separate KBO weight candidate is
 d7b6a9dfff464eb32c17c314d4825d5b027f1b2d on origin/fix/kbo-definition-weights.
It is not on main and is not integrated, built or executed here. Its Natural
weights and lazy-map changes have a source assessment only. The current branch
still has the earlier positive-Int context-reversal finding. Run the exact
native regression after the repair lands on main. Do not mark it fixed from
source inspection. No false equality or termination cycle was established.
