import MicroCFTA.SourceCurrentSameSymbolEdgeStable

namespace MicroCFTA.SourceCurrentSameSymbolEdgeReady
open Cache Language InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks IntersectSchedule
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
variable {width : Nat}

/-! Complete only the published ready paths. Both-miss admission remains separate. -/
local notation "run" => SourceCurrentSameSymbolEdgeControl.execute
local notation "advance" => SourceCurrentSameSymbolEdgeControl.step

private theorem read_ready
    (semanticView : View Symbol) (model : InputMeaning semanticView)
    (ranked : RankedInput semanticView model.valid) (holds : Guard → Term Symbol → Bool)
    (left right : Edge) (before : Wrapper width)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (stable : SourceCurrentSameSymbolEdgeStable.Stable semanticView model ranked holds before)
    (leftResident : EdgeResident before.checked.native.machine.heap left)
    (rightResident : EdgeResident before.checked.native.machine.heap right)
    (handle : Nat) (present : before.memo.table (left.entry.identity, right.entry.identity) = some handle) :
    ∃ result, before.memo.cells handle = some ⟨(left, right), .returned result⟩ ∧
      EdgeResident before.checked.native.machine.heap result ∧
      (let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
       SourceCurrentAllocatedNativeContextCache.EdgeLaw semanticView model ranked holds
         ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩ result) := by
  obtain ⟨⟨⟨capturedLeft, capturedRight⟩, status⟩, stored, keys⟩ :=
    stable.valid.linked (left.entry.identity, right.entry.identity) handle present
  obtain ⟨result, phase⟩ := stable.returned handle _ stored
  change status = .returned result at phase
  subst status
  obtain ⟨first, second, spec⟩ := stable.valid.checked handle _ stored
  have leftIdentity : capturedLeft.entry.identity = left.entry.identity := congrArg Prod.fst keys
  have rightIdentity : capturedRight.entry.identity = right.entry.identity := congrArg Prod.snd keys
  have leftSame := edge_identity_unique _ coherent capturedLeft left first leftResident leftIdentity
  have rightSame := edge_identity_unique _ coherent capturedRight right second rightResident rightIdentity
  subst capturedLeft
  subst capturedRight
  exact ⟨result, stored, spec.1, spec.2⟩

private theorem reverse_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (left right result : Edge) (before : Wrapper width) (handle : Nat)
    (missing : before.memo.table (left.entry.identity, right.entry.identity) = none)
    (reverse : before.memo.table (right.entry.identity, left.entry.identity) = some handle)
    (stored : before.memo.cells handle = some ⟨(right, left), .returned result⟩)
    (bounded : handle < before.memo.next) (swap : right.entry.identity < left.entry.identity) :
    ∃ after : Wrapper width, run 7 (.call (left, right) []) before = .done result after ∧
      after.checked = before.checked := by
  let published := (FlatMemoThunk.lookupOrInsert
    (left.entry.identity, right.entry.identity) (left, right) before.memo).2
  let middle : Wrapper width := {before with memo := published}
  let running := FlatMemoThunk.setStatus before.memo.next .evaluating published
  let current : Wrapper width := {before with memo := running}
  let after : Wrapper width :=
    {current with memo := FlatMemoThunk.finish before.memo.next result current.memo}
  have allocated : published.cells before.memo.next = some ⟨(left, right), .suspended⟩ :=
    (FlatMemoThunk.lookup_miss (left.entry.identity, right.entry.identity) (left, right) before.memo missing).2.2
  have demanded : FlatMemoThunk.demand before.memo.next published = (.evaluate (left, right), running) := by
    simp only [FlatMemoThunk.demand, allocated, running]
  have currentTable : current.memo.table =
      put before.memo.table (left.entry.identity, right.entry.identity) before.memo.next := by
    simp only [current, running, FlatMemoThunk.setStatus, allocated]
    simp only [published, FlatMemoThunk.lookupOrInsert, missing]
  have fresh : handle ≠ before.memo.next := Nat.ne_of_lt bounded
  have publishedStored : published.cells handle = some ⟨(right, left), .returned result⟩ := by
    simpa only [published, FlatMemoThunk.lookupOrInsert, missing, put, ite_eq_right fresh] using stored
  have currentStored : current.memo.cells handle = some ⟨(right, left), .returned result⟩ := by
    simp only [current, running, FlatMemoThunk.setStatus, allocated]
    simpa only [put, ite_eq_right fresh] using publishedStored
  have different : (right.entry.identity, left.entry.identity) ≠ (left.entry.identity, right.entry.identity) := by
    intro equal
    have identities := congrArg Prod.fst equal
    omega
  have currentReverse : current.memo.table (right.entry.identity, left.entry.identity) = some handle := by
    rw [currentTable]
    simpa only [put, ite_eq_right different] using reverse
  have looked : advance (.call (left, right) []) before =
      .yielded (.demand before.memo.next []) middle := by
    change SourceCurrentSameSymbolEdgeControl.Outcome.yielded
      (.demand (FlatMemoThunk.lookupOrInsert (left.entry.identity, right.entry.identity)
        (left, right) before.memo).1 []) middle = _
    exact congrArg (fun selected => SourceCurrentSameSymbolEdgeControl.Outcome.yielded
      (.demand selected []) middle)
      (FlatMemoThunk.lookup_miss (left.entry.identity, right.entry.identity) (left, right) before.memo missing).1
  have started : advance (.demand before.memo.next []) middle =
      .yielded (.order before.memo.next (left, right) []) current := by
    simp only [SourceCurrentSameSymbolEdgeControl.step, middle, demanded, current]
  have ordered : advance (.order before.memo.next (left, right) []) current =
      .yielded (.call (right, left) [before.memo.next]) current := by
    simp only [SourceCurrentSameSymbolEdgeControl.step, swap, ↓reduceIte]
  have reverseLooked : advance (.call (right, left) [before.memo.next]) current =
      .yielded (.demand handle [before.memo.next]) current := by
    simp only [SourceCurrentSameSymbolEdgeControl.step,
      FlatMemoThunk.lookup_hit (right.entry.identity, left.entry.identity) (right, left) current.memo handle currentReverse]
  have reverseDemanded : advance (.demand handle [before.memo.next]) current =
      .yielded (.ret result [before.memo.next]) current := by
    simp only [SourceCurrentSameSymbolEdgeControl.step,
      FlatMemoThunk.demand_ready handle current.memo (right, left) result currentStored]
  have returned : advance (.ret result [before.memo.next]) current = .yielded (.ret result []) after := rfl
  have finished : advance (.ret result []) after = .done result after := rfl
  refine ⟨after, ?_, rfl⟩
  simp only [SourceCurrentSameSymbolEdgeControl.execute, looked, started, ordered,
    reverseLooked, reverseDemanded, returned, finished]

/-- Complete a ready pair comparison and retain its canonical result law and memo records. -/
theorem ready_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (semanticView : View Symbol) (model : InputMeaning semanticView)
    (ranked : RankedInput semanticView model.valid) (holds : Guard → Term Symbol → Bool)
    (left right : Edge) (before : Wrapper width)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (stable : SourceCurrentSameSymbolEdgeStable.Stable semanticView model ranked holds before)
    (leftResident : EdgeResident before.checked.native.machine.heap left)
    (rightResident : EdgeResident before.checked.native.machine.heap right)
    (present :
      (∃ handle, before.memo.table (left.entry.identity, right.entry.identity) = some handle) ∨
      (∃ handle, before.memo.table (right.entry.identity, left.entry.identity) = some handle)) :
    ∃ (result : Edge) (after : Wrapper width),
      SourceCurrentSameSymbolEdgeControl.execute 7 (.call (left, right) []) before =
        .done result after ∧
      after.checked = before.checked ∧
      EdgeResident after.checked.native.machine.heap result ∧
      (let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
       SourceCurrentAllocatedNativeContextCache.EdgeLaw semanticView model ranked holds
         ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩ result) ∧
      SourceCurrentSameSymbolEdgeStable.Stable semanticView model ranked holds after ∧
      Cache.Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo := by
  have progress :
      ∃ (result : Edge) (after : Wrapper width),
        run 7 (.call (left, right) []) before = .done result after ∧
        after.checked = before.checked ∧
        EdgeResident before.checked.native.machine.heap result ∧
        (let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
         SourceCurrentAllocatedNativeContextCache.EdgeLaw semanticView model ranked holds
           ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩ result) := by
    cases found : before.memo.table (left.entry.identity, right.entry.identity) with
    | some handle =>
        obtain ⟨result, stored, resident, law⟩ :=
          read_ready semanticView model ranked holds left right before coherent stable leftResident rightResident handle found
        have looked : advance (.call (left, right) []) before = .yielded (.demand handle []) before := by
          simp only [SourceCurrentSameSymbolEdgeControl.step,
            FlatMemoThunk.lookup_hit (left.entry.identity, right.entry.identity) (left, right) before.memo handle found]
        have demanded : advance (.demand handle []) before = .yielded (.ret result []) before := by
          simp only [SourceCurrentSameSymbolEdgeControl.step,
            FlatMemoThunk.demand_ready handle before.memo (left, right) result stored]
        have finished : advance (.ret result []) before = .done result before := rfl
        refine ⟨result, before, ?_, rfl, resident, law⟩
        simp only [SourceCurrentSameSymbolEdgeControl.execute, looked, demanded, finished]
    | none =>
        have reversePresent : ∃ handle, before.memo.table (right.entry.identity, left.entry.identity) = some handle := by
          rcases present with ⟨handle, original⟩ | ⟨handle, reverse⟩
          · rw [found] at original
            cases original
          · exact ⟨handle, reverse⟩
        obtain ⟨handle, reverse⟩ := reversePresent
        have swap : right.entry.identity < left.entry.identity := by
          by_contra denied
          obtain ⟨canonical, canonicalPresent⟩ :=
            stable.canonical right.entry.identity left.entry.identity handle reverse
          by_cases forward : left.entry.identity < right.entry.identity
          · have original : before.memo.table (left.entry.identity, right.entry.identity) = some canonical := by
              simpa only [forward, ↓reduceIte] using canonicalPresent
            rw [found] at original
            cases original
          · have same : left.entry.identity = right.entry.identity := by omega
            have original : before.memo.table (left.entry.identity, right.entry.identity) = some handle := by
              simpa only [same] using reverse
            rw [found] at original
            cases original
        obtain ⟨result, stored, resident, law⟩ :=
          read_ready semanticView model ranked holds right left before coherent stable rightResident leftResident handle reverse
        have bounded := stable.valid.bounded handle _ stored
        obtain ⟨after, done, same⟩ := reverse_ready left right result before handle found reverse stored bounded swap
        have forward : ¬ left.entry.identity < right.entry.identity := by omega
        refine ⟨result, after, done, same, resident, ?_⟩
        simpa only [swap, forward, ↓reduceIte] using law
  obtain ⟨result, after, done, same, resident, law⟩ := progress
  have resultResident : EdgeResident after.checked.native.machine.heap result := by
    simpa only [same] using resident
  have growth : Extension before.checked.native.machine after.checked.native.machine := by
    rw [same]
    exact Extension.refl _
  obtain ⟨finalStable, extension, history⟩ :=
    SourceCurrentSameSymbolEdgeStable.completed_preserves semanticView model ranked holds 7 left right result
      before after stable leftResident rightResident done growth resultResident law
  exact ⟨result, after, done, same, resultResident, law, finalStable, extension, history⟩

end MicroCFTA.SourceCurrentSameSymbolEdgeReady
