import MicroCFTA.SourceCurrentStoredPairedUnionLineage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.PairedUnionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredMuBinderChildLineage (Paired Slot)
open SourceCurrentOpenObservationSurvival (Related)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)

private def captureSource : Syntax Nat Bool := .binder true (.union [.node [.mk 3 true []],.node [.mk 4 false [.var 0]]])
private def captureBuilt := build captureSource [] empty
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) := match outcome with | .done result _ => result | .pending .. => .empty
private def capture := value captureBuilt
private def base := captureBuilt.state
private def inner : Syntax Nat Bool := .node [.mk 8 false [.var 0,.var 1]]
private def rows : List (EdgeSyntax Nat Bool) :=
  [.mk 7 true [inner,.var 0,.var 1,.var 2],.mk 7 true [inner,.var 0,.var 1,.var 2],.mk 11 false [.var 3]]
private def mixed : Syntax Nat Bool := .union [.union [.var 0,.var 1],.node rows,.var 2,.empty,.var 0]
private def dead : Syntax Nat Bool := .union [.node [.mk 7 true [.var 0]],.node [.mk 8 false [.var 1]],.empty]
private def firstInputs : List (Value Nat Bool) := [.reference (.uninterned 0),.reference (.uninterned 1),capture,.empty]
private def secondInputs : List (Value Nat Bool) := [.reference (.uninterned 9),.reference (.uninterned 10),capture,.empty]
private def firstEnvironment : Environment Nat Bool := fun name => if name = .uninterned 0 ∨ name = .uninterned 1 then some capture else none
private def secondEnvironment : Environment Nat Bool := fun name => if name = .uninterned 9 ∨ name = .uninterned 10 then some capture else none
private def eraseFirst : Environment Nat Bool := fun name => if name = .uninterned 0 ∨ name = .uninterned 1 then some .empty else none
private def eraseSecond : Environment Nat Bool := fun name => if name = .uninterned 9 ∨ name = .uninterned 10 then some .empty else none
private def isUnion : Value Nat Bool → Bool | .union .. => true | _ => false
private def isNode : Value Nat Bool → Bool | .node .. => true | _ => false
private def isMu : Value Nat Bool → Bool | .mu .. => true | _ => false

private theorem captureActual : captureBuilt = .done capture base := by cbv
private theorem baseReady : Ready base := SourceEqualityRequiredCache.constructed captureSource capture base captureActual
private theorem captureAvailable : Available base capture :=
  (InternedFreshOrdinaryFacts.build_verified captureSource [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result capture base captureActual
private theorem firstAvailable : InternedNestedProvenance.Values base firstInputs := by
  intro value member
  simp only [firstInputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact InternedNestedProvenance.ordinary_available _ _
  · exact InternedNestedProvenance.ordinary_available _ _
  · exact captureAvailable
  · exact InternedProbeProvenance.empty_available _
private theorem secondAvailable : InternedNestedProvenance.Values base secondInputs := by
  intro value member
  simp only [secondInputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact InternedNestedProvenance.ordinary_available _ _
  · exact InternedNestedProvenance.ordinary_available _ _
  · exact captureAvailable
  · exact InternedProbeProvenance.empty_available _

private theorem paired (first second : Environment Nat Bool)
    (ownFirst : Slot first second (.reference (.uninterned 0)) (.reference (.uninterned 9)))
    (outer : Slot first second (.reference (.uninterned 1)) (.reference (.uninterned 10))) :
    Paired first second firstInputs secondInputs := by
  refine .cons ownFirst (.cons outer (.cons ?_ (.cons ?_ .nil)))
  · change Slot first second capture capture
    have closed : capture.free = [] := by cbv
    have actualMu : isMu capture = true := by cbv
    cases shape : capture <;> simp only [shape,isMu] at actualMu
    all_goals try {cases actualMu}
    refine ⟨rfl,?_⟩
    intro name present
    rw [shape] at closed
    rw [closed] at present
    cases present
  · exact ⟨rfl,by simp [Value.free]⟩

private theorem firstReplacements : Replacements base firstEnvironment := by
  intro name output found
  dsimp only [firstEnvironment] at found
  split at found
  · cases found; exact captureAvailable
  · cases found
private theorem secondReplacements : Replacements base secondEnvironment := by
  intro name output found
  dsimp only [secondEnvironment] at found
  split at found
  · cases found; exact captureAvailable
  · cases found
private theorem eraseFirstReplacements : Replacements base eraseFirst := by
  intro name output found
  dsimp only [eraseFirst] at found
  split at found
  · cases found; exact InternedProbeProvenance.empty_available _
  · cases found
private theorem eraseSecondReplacements : Replacements base eraseSecond := by
  intro name output found
  dsimp only [eraseSecond] at found
  split at found
  · cases found; exact InternedProbeProvenance.empty_available _
  · cases found

/-- Initial paired data constructs raw and stored mixed union calls with a productive Mu capture. -/
private theorem mixed_receipt :
    ∃ rawFirst after rawSecond common left middle right reader,
      build mixed firstInputs base = .done rawFirst after ∧
      build mixed secondInputs after = .done rawSecond common ∧
      execute rawFirst firstEnvironment common = .done left middle ∧
      execute rawSecond secondEnvironment middle = .done right reader ∧
      execute rawFirst firstEnvironment reader = .done left reader ∧
      execute rawSecond secondEnvironment reader = .done right reader ∧
      Keeps base after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right ∧
      firstInputs.tail ≠ secondInputs.tail ∧ isMu capture = true ∧
      isUnion rawFirst = true ∧ isUnion rawSecond = true ∧ isUnion left = true := by
  have free : BinderFree mixed := by simp [mixed,rows,inner,BinderFree,ManyBinderFree,EdgesBinderFree]
  obtain ⟨rawFirst,after,rawSecond,common,left,middle,right,reader,firstRaw,secondRaw,firstDone,secondDone,
    firstWarm,secondWarm,firstKept,secondKept,firstStored,secondStored,leftAvailable,rightAvailable,
    firstHistory,secondHistory,related⟩ := SourceCurrentStoredPairedUnionLineage.initial mixed free firstInputs secondInputs
      firstEnvironment secondEnvironment (paired _ _ rfl rfl) base baseReady firstAvailable secondAvailable
      firstReplacements secondReplacements
  have knownFirst : build mixed firstInputs base = .done (value (build mixed firstInputs base)) (build mixed firstInputs base).state := by cbv
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (firstRaw.symm.trans knownFirst)
  have knownSecond : build mixed secondInputs (build mixed firstInputs base).state =
      .done (value (build mixed secondInputs (build mixed firstInputs base).state))
        (build mixed secondInputs (build mixed firstInputs base).state).state := by cbv
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (secondRaw.symm.trans knownSecond)
  have positive : isUnion left = true := by
    have known : (match execute (value (build mixed firstInputs base)) firstEnvironment
      (build mixed secondInputs (build mixed firstInputs base).state).state with | .done output _ => isUnion output | _ => false) = true := by cbv
    simpa only [firstDone] using known
  exact ⟨_,_,_,_,left,middle,right,reader,firstRaw,secondRaw,firstDone,secondDone,firstWarm,secondWarm,
    firstKept,secondKept,firstStored,secondStored,leftAvailable,rightAvailable,firstHistory,secondHistory,related,
    (by intro same; have heads := congrArg List.head? same; cases heads),by cbv,by cbv,by cbv,positive⟩

/-- Initial paired erasure makes both normalized ordinary unions return physical Empty. -/
private theorem dead_receipt :
    ∃ rawFirst after rawSecond common left middle right reader,
      build dead firstInputs base = .done rawFirst after ∧ build dead secondInputs after = .done rawSecond common ∧
      execute rawFirst eraseFirst common = .done left middle ∧ execute rawSecond eraseSecond middle = .done right reader ∧
      Keeps base after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Related left right ∧ isNode rawFirst = true ∧ isNode rawSecond = true ∧
      left.referenceOf = .empty ∧ right.referenceOf = .empty := by
  have free : BinderFree dead := by simp [dead,BinderFree,ManyBinderFree,EdgesBinderFree]
  obtain ⟨rawFirst,after,rawSecond,common,left,middle,right,reader,firstRaw,secondRaw,firstDone,secondDone,
    firstWarm,secondWarm,firstKept,secondKept,firstStored,secondStored,leftAvailable,rightAvailable,
    firstHistory,secondHistory,related⟩ := SourceCurrentStoredPairedUnionLineage.initial dead free firstInputs secondInputs
      eraseFirst eraseSecond (paired _ _ rfl rfl) base baseReady firstAvailable secondAvailable
      eraseFirstReplacements eraseSecondReplacements
  have knownFirst : build dead firstInputs base = .done (value (build dead firstInputs base)) (build dead firstInputs base).state := by cbv
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (firstRaw.symm.trans knownFirst)
  have knownSecond : build dead secondInputs (build dead firstInputs base).state =
      .done (value (build dead secondInputs (build dead firstInputs base).state))
        (build dead secondInputs (build dead firstInputs base).state).state := by cbv
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (secondRaw.symm.trans knownSecond)
  have firstEmpty : left.referenceOf = .empty := by
    have known : (match execute (value (build dead firstInputs base)) eraseFirst
      (build dead secondInputs (build dead firstInputs base).state).state with | .done output _ => output.referenceOf | _ => .empty) = .empty := by cbv
    simpa only [firstDone] using known
  exact ⟨_,_,_,_,left,middle,right,reader,firstRaw,secondRaw,firstDone,secondDone,firstKept,secondKept,
    firstStored,secondStored,related,by cbv,by cbv,firstEmpty,related.1.mp firstEmpty⟩

/-- The actual initial-data integration retains this exact checked receipt. -/
theorem mixed_union_initial :
    ∃ rawFirst after rawSecond common left middle right reader,
      build mixed firstInputs base = .done rawFirst after ∧
      build mixed secondInputs after = .done rawSecond common ∧
      execute rawFirst firstEnvironment common = .done left middle ∧
      execute rawSecond secondEnvironment middle = .done right reader ∧
      execute rawFirst firstEnvironment reader = .done left reader ∧
      execute rawSecond secondEnvironment reader = .done right reader ∧
      Keeps base after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right ∧
      firstInputs.tail ≠ secondInputs.tail ∧ isMu capture = true ∧
      isUnion rawFirst = true ∧ isUnion rawSecond = true ∧ isUnion left = true := mixed_receipt

/-- The actual initial-data integration retains this exact checked receipt. -/
theorem ordinary_union_empty :
    ∃ rawFirst after rawSecond common left middle right reader,
      build dead firstInputs base = .done rawFirst after ∧ build dead secondInputs after = .done rawSecond common ∧
      execute rawFirst eraseFirst common = .done left middle ∧ execute rawSecond eraseSecond middle = .done right reader ∧
      Keeps base after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Related left right ∧ isNode rawFirst = true ∧ isNode rawSecond = true ∧
      left.referenceOf = .empty ∧ right.referenceOf = .empty := dead_receipt

end MicroCFTA.PairedUnionKernels
