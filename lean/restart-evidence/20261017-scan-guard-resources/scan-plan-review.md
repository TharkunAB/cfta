# Initial Scan composition plan

This review covers the current checked Scan. The existing initial gate, supported Seeded, and supplied-alphabet memo producers give the required local completions. The next theorem must compose these producers in source order. It must derive its own actual Scan and strict reads. It must not take `Ranges`, `SeededRanges`, a completed Scan, or bounds at future heaps as an entry premise.

## Source order and exact states

`SourceCurrentAllocatedScanWorker.scan` has five independent fuel arguments `g s p h n` and a separate fixed conjunction admission `budget`. It executes the primary gate first. A false primary answer selects the class and runs the suffix. A true primary answer runs the secondary gate. A true secondary answer skips the class. A false secondary answer executes the first-seeded query and then the current fourth-memo call. A true memo answer stops before the suffix. A false memo answer runs the suffix. The selected output retains source order and multiplicity.

The exact heap offsets in `ClassScan.Scan` are:

1. Primary returns `heap`. The checked return is `advanceHeap before heap`.
2. Secondary starts at that checked return and returns `anchor`. The checked return is `advanceHeap (advanceHeap before heap) anchor`.
3. Seeded starts at the second checked return and returns the whole checked state `middle`.
4. The fourth memo starts at `physical middle` and returns the physical state `later` and memo `saved`.
5. The suffix starts at `advancePhysical middle later` and `saved`.

`advanceHeap` retains equality operations, native cells, and domains. `advancePhysical` retains native cells and domains but uses the actual returned equality-operation state. The Seeded query can change native cells, domains, equality operations, and the input inventory. It must not be replaced by a constructor-only advance. The outer caller advance retains both outer result-table families and the Merge memo. Only the memo-call phase can update the fourth memo.

## Existing local endpoints

`GateFrameResources.primary` and `.secondary` start from Frame, Fits, and availability of the original forest. They construct the actual gate graph, Frame at the exact checked return, Fits at `forecast paths profile`, physical effects, original forest availability, and successful replay at every gate fuel above `workerFuel paths profile`. They add no whole-forest closedness or finite-cap premise.

`SecondaryProjectionScoped.class_support` derives support from the actual false secondary graph. Its anchor is the actual final secondary heap. It derives anchor semantic readiness, gate readiness, growth, availability of the original forest, and `PathSupport` for every original signed path. The native producer must use this anchor. It must not rebase the support to an arbitrary later heap. Growth from the anchor to the exact second-gate checked state is reflexive. The support permits unrelated open siblings.

`SeededCallerNumeric.complete` takes those initial anchor facts, Context, Frame, Fits, proper signed paths, and a pure Seeded reservation. It constructs Seeded, exact SeededReads, the full checked receipt, full caller Post, final Fits, inclusion for a nonempty class, and three independently larger projection/read/native replays. It preserves the first seed by evaluating the remaining path projections before the original seed is combined. It does not use Merge as a substitute for native intersection. It requires no finite input cap.

`ConjunctionAlphabetBounds.caller_complete` takes one finite supplied guard alphabet, its current heap annotation, Context, Frame, Fits, and an available query. It constructs the actual current memo hit or miss. It returns full Post, Frame, numeric Fits, the retained guard carrier, answer soundness, and independently larger projection/read replays. Its algorithmic admission budget stays fixed. A false answer has no acceptance or completeness claim.

## Exact read bundles and full Post

A numeric graph producer does not by itself give the strict final global memo bundle. `AllocatedPrimaryReads.lift_class` constructs exact primary ClassReads and returned memo validity. `SecondaryMemos.lift_class` does the same for the actual secondary graph. Thread each returned bundle to the next phase.

The Seeded producer already returns its exact SeededReads and final bundle. For the memo phase, `AlphabetBounds.caller_complete` retains validity of the unchanged logical bundle in its Post. The actual `ConjunctionGlobalMemos.call_memos` can advance the unfolding bundle. Use the produced actual Call with `AllocatedConjunctionCaller.actual` to obtain exact CallReads and Post at that returned bundle. Keep the independently proved numeric Fits, Frame, and worker replay. Do not identify these two bundles without a proof.

`QueryReads.run` combines the actual secondary, Seeded, and memo reads. `AllocatedScanSourceReads.ScanReads` combines those query reads with source-aligned primary reads and the reached suffix reads. Its erasure gives the older Scan read interface. `PartialInvariant.Post.trans` composes stages even when a Seeded query changes the inventory. Gate and memo effects transport the earlier outer soundness, Merge stored law, CacheCovers, fourth correctness, and probe history. They preserve original forest availability by actual growth.

The older whole-Scan `finite`, `verified`, and global-memo theorems still take reached `Ranges`. They are source patterns, not the intended new initial endpoint. Either derive those plans internally from the initial schedule, or assemble the same graph, Post, reads, and soundness directly from the local produced receipts. Exposing the old plan at entry would leave the main obligation open.

## Noncircular pure schedule

Carry a pure pair `(profile, alphabet)` through the initial class list. Let `signed paths := paths.map (List.map Int.ofNat)`. For a class, predict primary profile `p1 := Gate.forecast paths p`, secondary profile `p2 := Gate.forecast paths p1`, then the literal Seeded fold schedule at `p2`. Predict the memo profile with `AlphabetBounds.callerForecast returnedAlphabet budget p3`, where `p3` is the Seeded final profile. Continue the suffix from this same all-work class profile.

The Seeded alphabet schedule must use the same order as its profile schedule. For a singleton fold, apply `projectionProfile seed count` and retain the alphabet. For a cons fold, apply the head projection profile, recursively predict the tail, then predict the native query. At that native entry profile `q`, update the profile by `ResourceForecast.step q` and update the alphabet by `NativeGuardAlphabet.advance alphabet (instructionBound q.nodes q.edges q.mass)`. The query producer must prove this carrier update from its own actual physical trace and initial instruction ceiling. Projection and memo phases retain their entry carrier.

The alphabet helper proves only pure extension laws. One extension has not been proved sufficient for a whole query. Root's planned physical proof advances the carrier at each yielded checked instruction, then uses `advance_count_mono` and the initial instruction bound. The old guard list from the Scan entry is insufficient after native conjunction emits a new guard. Recomputing a guard carrier at the reached heap is also not an initial forecast.

Do not define the final carrier using an instruction bound at the unknown final profile while that profile itself depends on the carrier. The forward pair schedule above has no such cycle. Its initial carrier comes from actual original edge payloads via `ConjunctionGuardUniverse.initial`.

Pad early branches to the all-work class forecast with `Fits.mono` and carrier inclusion. A selected branch has the primary profile. A skipped branch has the secondary profile. Both are below the predicted full class profile. Invoke the tail at the predetermined padded profile. This technique does not require recomputing the schedule from an actual returned heap. A stopped branch needs no actual suffix. It may widen its final bound to the pure whole-list forecast.

One Room condition at the final pure profile bounds each predicted native entry by profile inflation. For empty classes, a reservation predicate can be True. For nonempty schedules, a single final Room is conservative and initial. The entry forest count stays fixed throughout Scan because the worker reuses the original `values`; it is not the number of query-generated values.

## Worker ceilings and proposed endpoint

At a predicted class entry, the primary ceiling is `Gate.workerFuel paths p`. The secondary ceiling is `Gate.workerFuel paths p1`. Let `seedFuel := SeededForecast.fuel count (signed paths) p2`. Let the memo ceilings be `WorklistResources.workerFuel alphabet3 budget (scalar p3)` and `readerFuel alphabet3 budget (scalar p3)`. The class projection ceiling is the maximum of seedFuel and memo worker fuel. Its reader ceiling is the maximum of seedFuel and memo reader fuel. Its native ceiling is seedFuel. Take componentwise maxima with the suffix ceilings. There is no extra Scan recursion decrement. The literal worker recurses structurally on the class list.

A minimal initial producer has the following shape. Names are a proposal, not new declarations in this survey.

```lean
complete formulas solver inventory budget values classes before memos
  (initial : Context formulas solver inventory before memos)
  (frame : Frame formulas solver inventory before.checked)
  (profile : Profile) (fits : Fits profile before.checked)
  (available : Values before.checked.native.machine.heap values)
  (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
  (active : ∀ paths ∈ classes, Nontrivial paths)
  (reserved : InitialScanReserved bits budget values.length classes profile initialAlphabet)
  : ∃ outcome selected after saved next final,
      ∃ actual : Scan budget unconstrained reaches values classes
          before.checked before.fourth outcome selected after saved,
        ScanSourceReads actual memos final ∧
        Post formulas solver next before (advance before after saved before.merge) final ∧
        Frame formulas solver next after ∧ Fits finalPureProfile after ∧
        Values after.native.machine.heap values ∧ selected.Sublist classes ∧
        StoppedSound formulas solver values classes outcome ∧
        ∀ G S P H N, enoughG → enoughS → enoughP → enoughH → enoughN →
          Worker.scan G S P H N budget values classes before.checked before.fourth =
            .done (outcome, selected) after saved
```

The initial alphabet is computed from the initial heap, rather than supplied as an arbitrary future alphabet. Root's actual native carrier theorem and the false-secondary support adapter are the remaining local inputs to this composition. The supplied-alphabet memo adapter is already frozen. The compiled direct readprobe checks all principal existing signatures and exits 0 without warnings.

For stopped soundness, combine the produced Seeded inclusion with the proper nonempty active class witness and the produced true memo AnswerSound. This avoids invoking the older Ranges-based refutation wrapper. Preserve the one-sided refusal statement. The result does not prove complete outer reduction, convergence, runtime demand or publication, or extraction. This review found no direct Haskell defect and changes no Haskell source.
