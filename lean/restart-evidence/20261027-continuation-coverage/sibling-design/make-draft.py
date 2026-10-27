from pathlib import Path
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
out=Path('/tmp/mcfta-continuation-coverage-20261027/sibling-design/drafts/v1/SourcePruningEnumerationFiniteSiblingCoverage.lean')
s=(root/'SourcePruningEnumerationFiniteSiblingResources.lean').read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationContinuationHead','import MicroCFTA.SourcePruningEnumerationContinuationHead\nimport MicroCFTA.SourcePruningEnumerationFiniteHeadCoverage\nimport MicroCFTA.SourcePruningEnumerationContinuationInvocation\nimport MicroCFTA.SourcePruningEnumerationNativeLanguage')
a=s.index('/-!'); b=s.index('namespace ',a)
s=s[:a]+'''/-!
# Coverage of an indexed finite recursive sibling scan

A supported original prefix either reaches the chosen accepting head or stops
at a strictly earlier recursive hook. The completed prefix fixes the occurrence
of each edge. Each event keeps its actual input and head memo states.
The chosen hook can stop after its head has been reached.
-/
'''+s[b:]
s=s.replace('open EnumerationState EnumerationSchedule','open EnumerationState EnumerationCorrectness EnumerationSchedule')
s=s.replace('local notation "Memos" => EndpointMemoGateTrace.Memos','local notation "Memos" => EndpointMemoGateTrace.Memos\nlocal notation "Queries" => SourceEndpointMemo.Memos\nlocal notation "Fragment" => Fragments.Fragment Symbol')
s=s.replace('/-- The original sibling schedule derives the actual scan with finite-depth callbacks and all reached certificates. -/\ntheorem alternatives_finite_complete_resources','/-- A supported indexed prefix reaches its accepting head or retains an exact earlier hook stop. -/\ntheorem alternatives_finite_complete_resources_accepting')
old='          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) := by'
append='''          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      ∀ extra,
        let work := bound + extra
        let hook := continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order work recursiveFuel)
          graph templates stop order work metadata uv
        ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint), selectedEdges[index]? = some chosen →
          (∀ earlier ∈ selectedEdges.take index, arityAllows earlier.children.length scs = true →
            SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none) →
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core →
            InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient chosen (assignment uv) →
            ∃ (eventIndex : Nat) (eventEdge : EdgeValue Symbol Constraint)
              (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
              (prefixReceipts : List (Receipt (bits + 2))) (prefixOutputs : List (Output (bits + 2) Typing))
              (fragment : Fragment) (branchCaller : Caller (bits + 2)) (branchQueries : Queries)
              (afterCache : Cached) (branchInventory : Inventory) (branchMemos : Memos),
              eventIndex ≤ index ∧ selectedEdges[eventIndex]? = some eventEdge ∧
              prefixReceipts.length = eventIndex ∧
              Post formulas solver headInventory caller headCaller headMemos ∧
              Packet formulas solver headInventory headCaller headMemos metadata before ∧
              Fits (stage recursiveFuel seed capturedMass inherited eventIndex).2 headCaller.checked ∧
              Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited eventIndex).1)
                headCaller.checked.native.machine.heap ∧
              SourcePruningEnumerationFiniteReservation.HeadReserved bits recursiveFuel
                (stage recursiveFuel seed capturedMass inherited eventIndex) capturedMass inherited ∧
              SourcePruningEnumerationNativeContinuations.run hook checkEmpty work work work work work
                uv scs before (selectedEdges.take eventIndex) caller memos.query =
                .complete prefixReceipts prefixOutputs headCaller headMemos.query ∧
              Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
              branchMemos.query = branchQueries ∧
              SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work uv scs
                eventEdge headCaller before headMemos.query =
                some (.complete fragment branchCaller branchQueries afterCache) ∧
              SourcePruningEnumerationHookInvocation.Invocation hook checkEmpty work work work work work
                uv scs before selectedEdges caller memos.query fragment branchCaller branchQueries afterCache ∧
              ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited eventIndex
                (.complete fragment branchCaller branchQueries afterCache) ∧
              ((eventIndex = index ∧ eventEdge = chosen ∧
                  ∃ extended : Nat → Language.Term Symbol,
                    (∀ old < before.core.counter, extended old = assignment old) ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient caller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended before.core ∧
                    Fragments.fill extended fragment = assignment uv ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient branchCaller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended afterCache.core) ∨
                (eventIndex < index ∧
                  ∃ (hookOutputs : List (Output (bits + 2) Typing)) (reason : Failure (bits + 2) Typing)
                    (reached : Option (Caller (bits + 2) × Queries)),
                    hook fragment branchCaller branchQueries afterCache = .stopped hookOutputs reason reached ∧
                    result = .stopped prefixReceipts (prefixOutputs ++ hookOutputs)
                      (.continuation (.complete fragment branchCaller branchQueries afterCache) reason reached) ∧
                    SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
                      (stage recursiveFuel seed capturedMass inherited (eventIndex + 1))
                      (.stopped hookOutputs reason reached))) := by'''
assert old in s
s=s.replace(old,append)
s=s.replace('fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl⟩','fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl, ?_⟩')
s=s.replace('      · intro output member\n        cases member\n  | cons edge rest ih =>','      · intro output member\n        cases member\n      · intro extra index chosen found\n        simp at found\n  | cons edge rest ih =>',1)
s=s.replace('headFits, headKnown, shape⟩ :=\n        SourcePruningEnumerationNativeHookResources.head_finite_complete_resources','headFits, headKnown, shape, headAccepting⟩ :=\n        SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_accepting')
s=s.replace('obtain ⟨unhandled, _allowed, _projected⟩ := unsupported','obtain ⟨unhandled, allowed, projected⟩ := unsupported')
s=s.replace('by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩⟩','by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩, ?_⟩',1)
needle='''        · intro output member
          cases member
      · have receiptCertificate'''
replace='''        · intro output member
          cases member
        · intro extra index chosen found supported ambient assignment satisfied accepted
          cases index with
          | zero =>
              have chosenSame : edge = chosen := Option.some.inj found
              subst chosen
              obtain ⟨extended, fragment, afterCache, _agree, _original, impossible, _filled, _final⟩ :=
                headAccepting ambient assignment satisfied accepted
              cases impossible
          | succ index =>
              exact (supported edge (by
                simp only [List.take_succ_cons, List.mem_cons]
                exact .inl trivial) allowed projected).elim
      · have receiptCertificate'''
assert needle in s;s=s.replace(needle,replace)
s=s.replace('tailKnown, tailLength, tailReceipts, tailOutputs, tailShape⟩ :=','tailKnown, tailLength, tailReceipts, tailOutputs, tailShape, tailAccepting⟩ :=')
s=s.replace('              ?_, ?_, ?_⟩\n            · intro extra','              ?_, ?_, ?_, ?_⟩\n            · intro extra',1)
needle='''                  certificate.prepend hookPost headOutputs⟩
        | stopped headOutputs reason reached =>'''
observer='''                  certificate.prepend hookPost headOutputs⟩
            · intro extra index chosen found supported ambient assignment satisfied accepted
              let w := bound + extra
              let hook := continueWith
                (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                graph templates stop order w metadata uv
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have continued : match (generalizing := false) receipt with
                  | .complete fragment actual queries after =>
                      hook fragment actual queries after = .complete headOutputs hookCaller hookQueries
                  | _ => advance receipt = some (hookCaller, hookQueries) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual queries after => exact hooked
                | unhandled => cases advanced
                | rejected actual queries after | stopped fragments observation candidate =>
                    obtain ⟨empty, actual, queries⟩ :=
                      SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                    exact ⟨by rw [actual, queries]; exact advanced, empty⟩
              cases index with
              | zero =>
                  have chosenSame : edge = chosen := Option.some.inj found
                  subst chosen
                  obtain ⟨extended, fragment, afterCache, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
                    headAccepting ambient assignment satisfied accepted
                  have observed : SourcePruningEnumerationCapturedEdge.run checkEmpty w w w w w
                      uv scs edge caller before memos.query =
                      some (.complete fragment middleCaller saved afterCache) := by
                    rw [completed] at first
                    exact first
                  refine ⟨0, edge, inventory, caller, memos, [], [], fragment, middleCaller, saved,
                    afterCache, middleInventory, middleMemos, Nat.le_refl _, rfl, rfl,
                    Post.refl packet.context, packet, bounded, known, reserved.head, rfl,
                    headPost, headQueries, observed, .here observed, ?_,
                    .inl ⟨rfl, rfl, extended, agree, originalSatisfied, filled, afterSatisfied⟩⟩
                  simpa only [completed] using receiptCertificate
              | succ index =>
                  have tailFound : rest[index]? = some chosen := by
                    simpa only [List.getElem?_cons_succ] using found
                  have tailSupported : ∀ earlier ∈ rest.take index,
                      arityAllows earlier.children.length scs = true →
                      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
                    intro earlier member allowed
                    exact supported earlier (by
                      simp only [List.take_succ_cons, List.mem_cons]
                      exact .inr member) allowed
                  have realized : SourcePruningEnumerationObservation.PendingRealized
                      caller.checked.native.machine.heap before.core := by
                    obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
                    exact realized
                  have middleSatisfied :=
                    (SourcePruningEnumerationNativeLanguage.satisfies_keeps
                      (SourceEqualityPCSGuard.holds formulas solver) ambient
                      caller.checked.native.machine.heap hookCaller.checked.native.machine.heap before.core
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      assignment realized hookPost.effects.keeps).mpr satisfied
                  have later := tailAccepting (headBound + extra) index chosen tailFound tailSupported
                    ambient assignment middleSatisfied accepted
                  have common : tailBound + (headBound + extra) = w := by dsimp [w, bound]; omega
                  rw [common] at later
                  obtain ⟨eventIndex, eventEdge, headInventory, headCaller, headMemos,
                    prefixReceipts, prefixOutputs, fragment, branchCaller, branchQueries, afterCache,
                    branchInventory, branchMemos, within, atIndex, prefixLength, inputPost, inputPacket,
                    inputFits, inputKnown, inputReserved, prefixRun, branchPost, branchQuery, observed,
                    _invocation, certificate, terminal⟩ := later
                  have liftedPrefix : SourcePruningEnumerationNativeContinuations.run hook
                      checkEmpty w w w w w uv scs before ((edge :: rest).take (eventIndex + 1))
                      caller memos.query = .complete (receipt :: prefixReceipts)
                        (headOutputs ++ prefixOutputs) headCaller headMemos.query := by
                    have running := SourcePruningEnumerationNativeContinuations.continued_head hook
                      checkEmpty w w w w w uv scs before edge (rest.take eventIndex) caller hookCaller
                      memos.query hookQueries receipt headOutputs first (by cases receipt <;> exact continued)
                    rw [←hookQuery, prefixRun] at running
                    simpa only [List.take_succ_cons] using running
                  have newAt : (edge :: rest)[eventIndex + 1]? = some eventEdge := by
                    simpa only [List.getElem?_cons_succ] using atIndex
                  have split : (edge :: rest) = (edge :: rest).take (eventIndex + 1) ++
                      eventEdge :: (edge :: rest).drop (eventIndex + 2) := by
                    obtain ⟨inside, selectedAt⟩ := List.getElem?_eq_some_iff.mp newAt
                    have dropped := List.drop_eq_getElem_cons inside
                    rw [selectedAt] at dropped
                    rw [←dropped]
                    exact (List.take_append_drop (eventIndex + 1) (edge :: rest)).symm
                  have actualInvocation := SourcePruningEnumerationNativeContinuations.complete_prefix_invocation
                    hook checkEmpty w w w w w uv scs before ((edge :: rest).take (eventIndex + 1))
                    caller memos.query liftedPrefix eventEdge ((edge :: rest).drop (eventIndex + 2))
                    fragment branchCaller branchQueries afterCache observed
                  rw [←split] at actualInvocation
                  refine ⟨eventIndex + 1, eventEdge, headInventory, headCaller, headMemos,
                    receipt :: prefixReceipts, headOutputs ++ prefixOutputs, fragment, branchCaller,
                    branchQueries, afterCache, branchInventory, branchMemos, by omega, newAt,
                    by simpa only [List.length_cons] using congrArg (fun n => n + 1) prefixLength,
                    hookPost.trans inputPost, inputPacket, ?_, ?_, ?_, liftedPrefix,
                    branchPost, branchQuery, observed, actualInvocation, certificate.prepend hookPost, ?_⟩
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputFits
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputKnown
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputReserved
                  · rcases terminal with ⟨sameIndex, sameEdge, extended, agree, oldSatisfied, filled, afterSatisfied⟩ |
                        ⟨earlier, hookOutputs, reason, endpoint, stoppedHook, stoppedResult, stoppedResources⟩
                    · have originalSatisfied :=
                        (SourcePruningEnumerationNativeLanguage.satisfies_keeps
                          (SourceEqualityPCSGuard.holds formulas solver) ambient
                          caller.checked.native.machine.heap hookCaller.checked.native.machine.heap before.core
                          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                          extended realized hookPost.effects.keeps).mp oldSatisfied
                      exact .inl ⟨by omega, sameEdge, extended, agree, originalSatisfied, filled, afterSatisfied⟩
                    · refine .inr ⟨by omega, hookOutputs, reason, endpoint, stoppedHook, ?_, ?_⟩
                      · simp only [result, stoppedResult, List.append_assoc]
                      · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using
                          stoppedResources.post hookPost
        | stopped headOutputs reason reached =>'''
assert needle in s;s=s.replace(needle,observer)
s=s.replace('returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_⟩','returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_, ?_⟩')
needle='''                receiptCertificate, currentResources⟩⟩

end MicroCFTA'''
observer='''                receiptCertificate, currentResources⟩⟩
            · intro extra index chosen found supported ambient assignment satisfied accepted
              let w := headBound + extra
              have observed := headRun extra
              have invoked : SourcePruningEnumerationHookInvocation.Invocation
                  (continueWith
                    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                    graph templates stop order w metadata uv)
                  checkEmpty w w w w w uv scs before (edge :: rest) caller memos.query
                  fragment actual queries after := .here observed
              have inputPrefix : SourcePruningEnumerationNativeContinuations.run
                  (continueWith
                    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                    graph templates stop order w metadata uv)
                  checkEmpty w w w w w uv scs before ((edge :: rest).take 0) caller memos.query =
                  .complete [] [] caller memos.query := rfl
              have actualSame : actual = middleCaller ∧ queries = saved := by
                simp only [advance, Option.some.injEq, Prod.mk.injEq] at advanced
                exact ⟨advanced.1, advanced.2.trans headQueries⟩
              have localPost : Post formulas solver middleInventory caller actual middleMemos := by
                simpa only [actualSame.1] using headPost
              have localQuery : middleMemos.query = queries := actualSame.2.symm.trans headQueries.symm
              refine ⟨0, edge, inventory, caller, memos, [], [], fragment, actual, queries, after,
                middleInventory, middleMemos, by omega, rfl, rfl, Post.refl packet.context,
                packet, bounded, known, reserved.head, inputPrefix, localPost, localQuery,
                observed, invoked, receiptCertificate, ?_⟩
              cases index with
              | zero =>
                  have chosenSame : edge = chosen := Option.some.inj found
                  subst chosen
                  obtain ⟨extended, chosenFragment, chosenCache, agree, originalSatisfied,
                    completed, filled, afterSatisfied⟩ := headAccepting ambient assignment satisfied accepted
                  have equality := SourcePruningEnumerationSelectedEdge.Result.complete.inj completed
                  obtain ⟨rfl, _sameCaller, _sameQueries, rfl⟩ := equality
                  exact .inl ⟨rfl, rfl, extended, agree, originalSatisfied, filled, by
                    simpa only [actualSame.1] using afterSatisfied⟩
              | succ index =>
                  refine .inr ⟨by omega, headOutputs, reason, reached, callbackRun extra, ?_, ?_⟩
                  · rfl
                  · exact currentResources

end MicroCFTA'''
assert needle in s;s=s.replace(needle,observer)
out.write_text(s)
print(out)
print(len(s.splitlines()),len(s.encode()))
