# Current checkpoint: prepared point stability and local semantics

Source: `05570bab725e076f94d8371be1efa485c3877f9d` on `formalize`.
Read [notes-current-prepared-point-stability.md](notes-current-prepared-point-stability.md) first.
The full formalization goal remains open and active. Normal pushes to
`origin/formalize` remain authorized.

The existing history now derives original Fits, guard Heap and reservation at
the actual prepared opaque point. Completed opaque points are stable at larger
work bounds. The local opaque semantic theorem restores the original narrowed
model under its explicit retention and whole reached-state satisfaction gates.
Local ordinary-head and opaque-completion arity bridges also pass. This removes
the earlier proposed need for a second history type on the opaque-resource route.

The largest remaining attachment is the actual prepared sibling scan and its
callbacks. Earlier callbacks can change the aggregate native caller while they
emit no outputs. Prove arity for that endpoint and for each output in the finite
producer, with its original selectionMembers/selectionLength premises. A Post
growth fact or an output-only history induction does not supply this result.
Keep the prepared parent separate from the original decoded source.

All 16 new modules and Audit pass strict Lean 4.34.1 checks. The combined Audit
passes 4,479 jobs and 81,486 theorem dependencies. All 25 new public theorem
blocks have whole-block review. The previous public readback remains an exact
prefix. All 4,462 prior non-Audit Lean files, 311 prior stronger proof sources
and 817 current Haskell/Cabal files retain their recorded hashes.

No new Haskell defect or fix was established. No Haskell or Cabal source changed.
Keep the prior Haskell repair findings for external work. The callback gap is a
Lean proof task. Durable evidence is under
`lean/restart-evidence/20261028-prepared-point-stability`.

The earlier document body follows unchanged.

# Prepared history semantic gates: 2026-10-28

Source checkpoint: `1115481c15dec8193b8d0594366ee5d068c24331` on `formalize`.
The formalization goal remains open. Continue from this checkpoint after reboot.
The user authorizes normal pushes to `origin` on `formalize`.

## Top-level target

For supported public inputs and the stated solver and resource assumptions,
prove that each accepted rendered term satisfies its requested constrained tree
language. Prove operation preservation and accepted-output coverage. Connect
counting, ranking, unranking, and sampling to that language. Compare the Lean
source model with the optimized interned Haskell implementation. Keep the older
constructor and equality targets as secondary targets.

## Current claim

For each finite recursive depth covered by the original resource reservation,
the prepared driver has a stable result above a finite work-fuel bound.
It retains its endpoint resources and an admitted history for each emitted output.
If the initial stored suspended tries are canonical, every emitted output retains
that property. The new finite theorem calls the existing finite producer once.
It retains the same bound, result, resource certificate, and histories.
It does not require a supplied future history or a supplied endpoint arity fact.

`Canonical` means that each stored suspended trie has a valid finite-map
representation. This is a storage property.

The new structural results derive the retained-child condition from the same
actual output's `Discharged` certificate. They transport isolated markers through
ordinary, terminal, opaque, parked, callback, and tail history paths. A parked
boundary and a nonterminal top opaque completion cannot lead to a wholly
discharged cache along the recorded path.

The local opaque semantic theorem now uses the original finite reservation and
the same stable actual completion receipt. It derives request ranges internally.
It keeps the original decoded value and the prepared value separate.
Its language-equivalence and retained-bucket premises remain explicit.
This is a local backward semantic theorem. It is not the whole-driver theorem.

`Discharged` applies to the whole cache. Successful rendering of one root does
not by itself supply this certificate. The public API connection remains open.
The finite theorem does not assert that any successful output exists.

## Changes in this checkpoint

The checkpoint adds 30 Lean modules and 30 Audit imports.
It adds 48 public theorems and one public observer definition.
It preserves all 4,432 earlier non-Audit Lean files and all 281 tracked stronger
proof-source files byte for byte.

| Commit | Change |
| --- | --- |
| `4a5fb9204d9e6f47ad3d71f518fbcef3fb0cb6b8` | Canonical storage through all prepared history tags and the finite producer |
| `123a92b274ea08c38641d47c2531f89c2233e794` | Preparation arity, backward arity reflection, and full native endpoint Posts |
| `46734b5d78de5a55e413e2cc53d8038708a8152b` | Terminal and history isolation; child retention from the actual discharged output |
| `698388e5fef08dba7ffbe1dd172e7b9616e8b4c0` | Local opaque semantics, stable opaque observer, and native point stability |
| `1115481c15dec8193b8d0594366ee5d068c24331` | Audit imports for all 30 new modules |

The source checkpoint is pushed. Documentation and full evidence follow in a
separate checkpoint commit. Use the branch tip for that final publication.

## Exact proof boundaries

1. `run_finite_complete_resources_with_history_canonical` takes the original
   `Packet`, `Fits`, known guards, selection conditions, initial suspended-mass
   bound, reservation, and initial `Canonical` fact. Its per-output history and
   canonical facts concern its own actual result. The theorem does not prove
   accepted-output coverage.
2. `ResourceHistory` and `SelectedHistoryReceipt` retain full native `Post`
   witnesses, the actual inventory, full memos, and query equality.
3. Preparation arity covers actual Mu unfolding and Union exposure and
   reconstruction. Projected arity uses resident prepared-parent edge records.
   Backward arity reflection requires an arity certificate at the reached
   endpoint. It does not establish forward arity for the whole driver from the
   initial input.
4. Terminal marker preservation uses actual dispatch, joins, and incoming writes.
   It does not require `ProperState`. The callback results and continuation cache
   are the ones retained by the same receipt and history.
5. `completed_head_output_retained` derives this exact condition for each child:
   the child is ordinary, its bucket contains a terminal trie, or its bucket is
   empty. It assumes `Discharged` for that same output. It does not prove
   `Discharged` for every output or assert backward `Satisfies` by itself.
6. `stable_complete_sound_retained_resources` assumes a stable actual opaque
   completion, prepared language equivalence, and the retained-bucket condition.
   It proves backward `Satisfies`, both value meanings, suspended obligations,
   and fragment filling for that completion. It does not substitute the decoded
   source value for the prepared value.
7. `OpaqueOutputStableHistoryAt` retains `OpaqueOutputHistoryAt` as its first
   conjunct. Its forget theorem is exact. Its producer retains every old producer
   result field and appends original resource evidence and stability for the same
   completion at each emitted output's own work fuel. The local producer still
   takes the smaller-depth `CompleteWithHistory` contract. The complete driver
   history does not yet retain the new observer.
8. Native index count, write, and finalizer stability covers successful point
   observations at larger fuel. Enabled emptiness stability covers completed
   checks. These lemmas do not establish arbitrary-call termination.

## Largest remaining proof gap

Complete the backward semantic induction over the actual prepared
`ResourceHistory`. The current history retains an opaque point observation.
It does not retain all stable resource evidence needed by the local opaque
semantic theorem. The new stable observer and its producer supply a checked
local construction, but the all-tag history still needs that evidence.

Also prove forward arity preservation from a genuine original input arity fact.
The new backward reflection lemmas can then recover the earlier arity gates.
Do not replace this obligation with an assumed final-output arity fact.

After this induction, connect the result to public rendering and accepted-output
coverage. Derive the required discharge condition from the intended public
success condition, or prove the appropriate reachable-state version. Keep that
domain explicit. Sufficient recursive depth, full API behavior, ranking,
unranking, sampling, and physical Haskell correspondence remain separate work.
The whole-system soundness and completeness theorem is not proved.

## Preferred next implementation

Keep the old source bytes and public readback prefix unchanged. Use additive
modules and an additive history observer or decoration with an exact forget
theorem. The current temporary evidence contains `opaque/ADDITIVE-ROUTE.md`.

1. Lift successful point stability through actual Dispatch, Fold, IncomingNode,
   cached adapters, TerminalPrefix, Terminal, ChildDispatch, and opaque finalizer
   calls. Use `SourceEqualityNativeDemand.done_stable`,
   `SourceCurrentAllocatedConjunctionWorkerActual.call_done_stable`,
   `UnionFind.findRoot_moreFuel`, and `SourceUnionFindRoot.root_moreFuel`.
   The new native-index and enabled-emptiness lemmas are already checked.
2. Recover narrowed admission from original `HistoryAdmission`, actual
   `PrefixValid`, and `PrefixAdmission.narrowed_admission`.
   Use `SelectedValueResources.fits_after` at the actual work fuel.
   Use actual stable preparation to identify the prepared caller and value.
3. Decorate the existing receipt and history at the same work fuel. Retain every
   old fact and the exact callback, returned inventory, full memos, and output.
   A finite wrapper must call the old all-depth producer once and retain its
   result. Do not add an external oracle for future histories or closure.
4. Prove the forward arity invariant and combine it with canonical storage,
   retained children, full Posts, and the new opaque evidence.
5. Finish the backward semantic induction and its public API connection.

A draft that strengthens three old contract files remains unapplied.
Do not apply it as a shortcut around preservation. A parallel decorated
callback/selected/all-depth producer induction is another option, but it copies
more proof structure.

## Validation and evidence

All 30 final module checks and the final Audit check pass with Lean 4.34.1,
`-DwarningAsError=true`, and `-Dlinter.all=true`.
The full Audit build passes with 4,463 jobs and 81,374 theorem dependency checks.
The complete public readback has 622 theorem signatures with axiom checks and
58 definitions. The only reported axioms are `Classical.choice`, `Quot.sound`,
and `propext`. The readback has no elision.

The complete readback is 2,760,282 bytes. Its SHA-256 is
`39f7ca1cd78f423054c5edbcc98394b5228660bd970b2621cd2201df369c1f5f`.
The prior 2,610,680 bytes are an exact prefix. The new 149,602-byte suffix has
SHA-256 `2dbe79c8953b18cb0b97801734ee241ef9b331f3ba6bb28f6149276accee5c23`.
All 49 new public blocks receive whole-block review against current source.

The full checkpoint evidence is under
`lean/restart-evidence/20261028-prepared-history-semantics/`.
Its README and standalone verifier specify the complete archive and manifest.
The archive retains failed drafts, all raw compiler logs, final exact source
inputs, strict reports, public readback, whole-block reviews, preservation
baselines, and resource measurements. Ten actual compiler/build failures and one
precompiler launch failure remain preserved. Every final check passes.

The current proof area is
`/tmp/mcfta-prepared-history-semantics-20261028`.
Treat it as immutable after its final `FROZEN.json` appears.
Do not write to either earlier frozen prepared-history area.
Use a fresh temporary area for later work. After reboot, extract into a fresh
directory with the standalone verifier. Do not reuse absent temporary state.

## Repairs and rejected approaches

Native opaque dispatch contains nested dependent matches. Splitting the outer
expression can descend into the native-value match and fail dependent
elimination. A separately elaborated match equation can also use a different
generated match helper. The checked proofs use a local finalizer helper with the
literal child-dispatch and Option-map equations. They reduce the native value
and guards before splitting the actual child-result match.

Other repaired Lean issues include namespace selection, reserved local names,
Boolean negation parsing, callback frame selection, equality orientation, and
key-by-key native Heap transfer through actual retained edge records. All failed
candidate bytes and full diagnostics remain in the evidence.

These are Lean proof repairs. No new Haskell implementation defect or fix was
established. No Haskell or Cabal file changed. All 817 current Haskell/Cabal
source files are unchanged. This set includes all 810 files in the inherited
baseline. The evidence records the denominator correction explicitly.
Keep actual Haskell defects and fixes in root `FINDINGS.md` for external work.

## Restart procedure

Read root `NEXT-PROMPT.md`, `HANDOFF.md`, `REBOOT-HANDOFF.md`, and `FINDINGS.md`.
Read this note and the new evidence README. Verify the archive before extraction.
Check the live branch, worktree, origin, and upstream. Pull with `--ff-only`.
The last observed upstream main is `d1ca06a1dd0c7488205feda613b529df21a08669`.
It is already an ancestor of this checkpoint. The LPO/KBO Natural fixes remain
integrated. Refresh upstream again before new proof work.

Use serial capped heavy jobs through `/home/tritlo/Code/heavy-management`.
Use a fresh `HEAVY_PEAKS` directory. The measured cap is 4 GiB for both memory
max and high, with zero swap. Keep compiler, native build, and benchmark work
serial. Do not use `sorry`, `admit`, custom axioms, `native_decide`, heartbeat or
recursion increases, or linter suppression. Read failed diagnostics in full
before repair. Use small commits and normal pushes to `formalize`.

The formalization goal remains active. This checkpoint does not pause or finish
it. There are no required live shell or network handles to resume.
