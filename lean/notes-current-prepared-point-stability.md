# Prepared point stability and local semantics: 2026-10-28

Source checkpoint: `05570bab725e076f94d8371be1efa485c3877f9d` on `formalize`.
The full formalization goal remains open and active.
The user authorizes normal pushes to `origin` on `formalize`.

## Top-level target

For supported public inputs and the stated solver and resource assumptions,
prove that each accepted rendered term belongs to its requested constrained
language. Prove operation preservation and accepted-output coverage. Connect
counting, ranking, unranking and sampling to that language. Compare the Lean
source model with the optimized interned Haskell implementation. Keep the older
constructor and equality targets as secondary targets.

## Strongest current statement

Under the existing original admission and selection assumptions, each finite
recursive depth covered by the original reservation has a result that is stable
above a finite work bound. Each emitted output has an admitted resource history.
If the initial stored equality tries are canonical, each output retains that
property. Canonical describes finite-map storage validity.

The new results recover original resources at each actual prepared opaque point.
A completed opaque or terminal point remains identical when any of its work
bounds increase. Under the explicit bucket-retention condition and whole reached
state satisfaction, the local opaque proof restores satisfaction of the original
narrowed state. It also proves the separate prepared and decoded source meanings,
the whole suspended bucket, and the fragment equation.

The new local ordinary-head and opaque-completion proofs preserve native arity
from each call's own input heap to its actual reached heap.
These results do not yet establish semantic soundness of every rendered output.
They do not establish whole-driver forward arity from the initial heap.

## Checked additions

There are 16 new modules and 25 new public theorems.

1. `SelectedPreparation.run_resources_known` uses the original Packet, stored
   handle, decoded lookup and literal preparation result. It derives the
   normalization Fits profile, prepared value mass and original guard Heap.
2. `HistoryAdmission.prepared_opaque_resources` uses the existing admission,
   actual PrefixValid and literal runPrefix equation. Prefix mass retention and
   the original reservation pay the actual suspended bucket cost. It derives
   Fits, original guard Heap and Reserved for that exact prepared call.
   This route needs no second history type.
3. Successful dispatch, fold, incoming, terminal, cache preparation, child
   dispatch and selected opaque points retain their complete observations at
   independently larger work bounds. Incoming and terminal stability retains
   the explicit clean empty/singleton row condition. Cache-dependent results
   retain the actual Some-cache condition. Exhausted error rows are excluded
   where a larger representative bound can change them.
4. `HistoryAdmission.prepared_opaque_sound_retained` composes the original
   resources, actual opaque completion, derived point stability and preparation
   identification. The source value and prepared value remain separate. The
   actual entered Packet, both preparation observations, opaque dispatch gate,
   retention condition and whole after-state Satisfies remain explicit.
5. `CompletedHeadReceipt.arity_after` uses the available closed prepared parent
   directly with SelectedEdgeResourcesArity. It aligns the actual selected and
   captured completions at a common work bound. It identifies the same reached
   caller through the actual finalizer.
6. `SelectedOpaqueDispatch.complete_heap` uses the actual child observation and
   finalizer equality. Its premises are original Packet/storage/availability,
   Fits, Reserved, original guard Heap, input arity Heap and literal completion.
   It requires no later arity premise or stable run family.

## The largest current proof gap

The prepared ordinary scan can execute earlier sibling callbacks before the
head retained in a selected output history. Its receipt stores a Post from the
prepared caller to that head's input caller. The local head theorem starts at
that input caller. A Post proves growth and its stated invariants. It does not
prove forward arity for new edge records.

The actual HookInvocation provenance retains the earlier head receipt and the
actual callback result. That callback can return a new aggregate native caller
with an empty output list. Histories for emitted outputs do not certify that
aggregate endpoint in the empty case. The selected history's tail induction
hypothesis concerns its own later callback, not every earlier sibling callback.

The next proof must preserve both the aggregate endpoint arity Heap and every
emitted output's Heap in the prepared finite producer. Use its original global
selectionMembers and selectionLength premises where the proof needs them.
CompleteWithHistory retains these global premises. Bare ResourceHistory does
not store them. Do not replace this task with arbitrary ResourceHistory plus an
assumed later Heap or an assumed forward Post rule.

The native intersection, conjunction, cap-edit, reduction and partial-worker
arity lemmas already exist. Prefix arity and actual selected preparation arity
also exist. The remaining work connects these local results through the actual
prepared scan and callbacks.

## Original arity admission

ArityOrigins.Heap constrains every stored edge key against that key's child
count. It is distinct from the guard annotation Heap used for Known.
constructed_heap_of_source derives it for the exact actual closed build from
empty with SourceChecked. That certificate includes normalized equality fields
and each actual accepted source constructor check at its syntactic child count.
Actual accepted and rejected MkEdge receipts preserve this invariant.

Packet and OriginPolicies do not contain that source-construction certificate.
Keep a genuine initial Heap or its exact source-construction derivation explicit.
The raw unprojectable-edge counterexample is not a Heap counterexample: its
missing projection makes the relevant Fits property vacuous. No full Packet or
supported Haskell-input counterexample was established here.

## Next proof sequence

1. Extend the actual prepared head resource producer with reached arity for
   every handled receipt shape. Keep the separate prepared parent. Do not apply
   an older captured-edge theorem that equates the stored source and parent.
2. Use the smaller-depth recursive producer for each actual callback. Retain
   the aggregate endpoint even when it emits no outputs. The older
   OutcomeResourcesWithArity and finite arity modules show this proof pattern.
   They do not prove execution identity with the prepared worker.
3. Induct over the actual sibling scan with these head and callback facts.
   Carry the original Packet, resource seed, full memos and reservation.
4. Add aggregate and per-output arity to the prepared finite producer's own
   result. Attach the derived facts to its unchanged output histories.
5. Complete backward semantic induction over those actual histories. Use the
   new original-resource opaque theorem and the checked same-output discharged
   retention lemmas. Keep the whole-cache Discharged premise explicit.
6. Connect public accepted rendering to the semantic premises. One rendered
   root alone is not the existing whole-cache Discharged certificate.
7. Prove accepted-output coverage and sufficient recursive depth. Complete the
   remaining public APIs and the physical Haskell correspondence proof.

Useful current sources include PreparedFiniteHistoryContract,
PreparedFiniteHistoryResources, PreparedFiniteCallbackResources,
PreparedFiniteSiblingResources, PreparedNativeHookResources, HookInvocation,
FiniteArityContract and FiniteResourcesArity in `lean/MicroCFTA`.

## Validation and preserved evidence

Lean 4.34.1 strict checks pass for the exact 16 new sources and Audit.
The flags are warningAsError and linter.all. Proof heartbeat and recursion
budgets did not increase. No linter suppression, sorry, admit, custom axiom or
native_decide was added. The combined Audit build passes with 4,479 jobs and
81,486 checked theorem dependencies. Only propext, Classical.choice and
Quot.sound appear in the checked public axiom lists.

Public readback contains 647 theorem signatures with axiom checks and 58
definitions. The previous 2,760,282-byte output is an exact prefix. The new
suffix has 59,997 bytes and 25 complete theorem blocks. The complete output
has 2,820,279 bytes and SHA-256
`532ea7283b67221f608d8d5f698739553ee2ebe43107f2ee730ffe24b7db3d0a`.
Each new public block has a whole-block source review.

All 4,462 prior non-Audit Lean sources, 311 prior stronger proof sources and
817 current Haskell/Cabal files retain their recorded hashes. The previous
complete checkpoint archive remains unchanged. Eleven prior document bodies
remain exact suffixes under the new status notes.

Five actual failed compiler/build commands remain with their full original
inputs and diagnostics. The repairs qualify State and constructor names, expose
known matches before rewriting, bind the exact cache equation before Prod.ext,
and keep forecast functions locally irreducible. The last repair avoids large
forecast reduction at the normal 200,000-heartbeat budget. All final checks pass.
The old unused `inputs` warning in InternedFreshOrdinaryClosedCompletion is
replayed by default Lake builds. Its old source is unchanged. New strict sources
and strict Audit have no warning failure.

Current work area: `/tmp/mcfta-prepared-point-stability-20261028`.
Durable evidence location:
`lean/restart-evidence/20261028-prepared-point-stability`.
The archive records exact source and documentation commits, immutable candidate
and audit reports, complete readbacks, failed attempts, source identities,
resource measurements and board receipts. Its README gives the standalone
verification and reconstruction command. Use a fresh destination.

All compiler and build jobs ran serially under heavy-management with measured
memory.max = memory.high = 4 GiB and memory.swap.max = 0. Use a new writable area
after a sealed checkpoint. Keep reconstructed and sealed inputs immutable.
No old process or tool handle should be resumed after reboot.

## Haskell and publication

This checkpoint establishes no new Haskell defect or fix. It changes no Haskell
or Cabal file and runs no Haskell check. Keep all prior Haskell repair findings
in root FINDINGS.md for external work. The callback proof gap above is a Lean
proof task. It is not a new Haskell defect finding.

Main remains `d1ca06a1dd0c7488205feda613b529df21a08669`, already integrated.
The earlier LPO and KBO Natural fixes remain included.
Normal pushes to origin/formalize remain authorized. Do not force-push.
The full goal remains active after this checkpoint.
