import MicroCFTA.SourceCurrentSameSymbolEdgeControl
import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceRecursiveIntersectionKernelFacts

namespace MicroCFTA.SourceCurrentSameSymbolEdgeStable
open Cache Language InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks IntersectSchedule
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
variable {width : Nat}

/-- A completed boundary retains exact pair links, resident records and canonical laws. -/
structure Stable (semanticView : View Symbol) (model : InputMeaning semanticView)
    (ranked : RankedInput semanticView model.valid) (holds : Guard → Term Symbol → Bool)
    (state : Wrapper width) : Prop where
  /-- The table links captured requests to resident cells with canonical result laws. -/
  valid : FlatMemoThunk.Valid
    (fun (pair : Edge × Edge) (key : Nat × Nat) =>
      (pair.1.entry.identity, pair.2.entry.identity) = key)
    (fun cell =>
      EdgeResident state.checked.native.machine.heap cell.request.1 ∧
      EdgeResident state.checked.native.machine.heap cell.request.2 ∧
      FlatMemoThunk.CellSpec (fun pair value =>
        let ordered := if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair
        EdgeResident state.checked.native.machine.heap value ∧
          SourceCurrentAllocatedNativeContextCache.EdgeLaw semanticView model ranked holds
            ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩ value) cell)
    state.memo
  /-- Every allocated cell has a returned result. -/
  returned : ∀ handle cell, state.memo.cells handle = some cell →
    ∃ value, cell.status = .returned value
  /-- Every published pair has its canonical ordered key. -/
  canonical : ∀ first second handle, state.memo.table (first, second) = some handle →
    ∃ orderedHandle, state.memo.table
      (if second < first then (second, first) else (first, second)) = some orderedHandle

/-! Preserve completed pair cells within one fixed semantic context. Native admission remains separate. -/
local notation "run" => SourceCurrentSameSymbolEdgeControl.execute
local notation "advance" => SourceCurrentSameSymbolEdgeControl.step
private abbrev Memo := FlatMemoThunk.State (Nat × Nat) (Edge × Edge) Edge
private def key (pair : Edge × Edge) := (pair.1.entry.identity, pair.2.entry.identity)
private def started (pair : Edge × Edge) (memo : Memo) : Memo :=
  ⟨put memo.table (key pair) memo.next, put memo.cells memo.next ⟨pair, .evaluating⟩, memo.next + 1⟩
private def written (pair : Edge × Edge) (value : Edge) (memo : Memo) : Memo :=
  ⟨put memo.table (key pair) memo.next, put memo.cells memo.next ⟨pair, .returned value⟩, memo.next + 1⟩

private theorem tail_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control next : SourceCurrentSameSymbolEdgeControl.Control)
    (before middle after : Wrapper width) (result : Edge)
    (one : advance control before = .yielded next middle) (done : run fuel control before = .done result after) :
    ∃ rest, run rest next middle = .done result after := by
  cases fuel with
  | zero => cases done
  | succ fuel => exact ⟨fuel, by simpa only [SourceCurrentSameSymbolEdgeControl.execute, one] using done⟩

private theorem ret_memo [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value result : Edge) (pending : List Nat) (before after : Wrapper width)
    (done : run fuel (.ret value pending) before = .done result after) :
    value = result ∧ after.memo = pending.foldl (fun memo handle => FlatMemoThunk.finish handle value memo) before.memo := by
  induction fuel generalizing pending before with
  | zero => cases done
  | succ fuel ih =>
      cases pending with
      | nil =>
          have same : value = result ∧ before = after := by
            simpa only [SourceCurrentSameSymbolEdgeControl.execute, SourceCurrentSameSymbolEdgeControl.step,
              SourceCurrentSameSymbolEdgeControl.Outcome.done.injEq] using done
          rcases same with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      | cons handle pending =>
          have tail : run fuel (.ret value pending) {before with memo := FlatMemoThunk.finish handle value before.memo} =
              .done result after := by simpa only [SourceCurrentSameSymbolEdgeControl.execute, SourceCurrentSameSymbolEdgeControl.step] using done
          obtain ⟨same, image⟩ := ih pending _ tail
          exact ⟨same, by simpa only [List.foldl] using image⟩

private theorem native_memo [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (body : SourceEqualityNativeDemand.Control Edge) (pending : List Nat)
    (before after : Wrapper width) (result : Edge)
    (done : run fuel (.native body pending) before = .done result after) :
    after.memo = pending.foldl (fun memo handle => FlatMemoThunk.finish handle result memo) before.memo := by
  induction fuel generalizing body before with
  | zero => cases done
  | succ fuel ih =>
      cases one : SourceEqualityNativeDemand.step body before.checked with
      | yielded next current =>
          apply ih next {before with checked := current}
          simpa only [SourceCurrentSameSymbolEdgeControl.execute, SourceCurrentSameSymbolEdgeControl.step, one] using done
      | done value current =>
          have tail : run fuel (.ret value pending) {before with checked := current} = .done result after := by
            simpa only [SourceCurrentSameSymbolEdgeControl.execute, SourceCurrentSameSymbolEdgeControl.step, one] using done
          obtain ⟨rfl, image⟩ := ret_memo fuel value result pending _ after tail
          exact image
      | failed | constraintError | blocked =>
          simp only [SourceCurrentSameSymbolEdgeControl.execute, SourceCurrentSameSymbolEdgeControl.step, one] at done; cases done

private theorem overwrite_cells (cells : Table Nat (FlatMemoThunk.Cell (Edge × Edge) Edge))
    (handle : Nat) (first second : FlatMemoThunk.Cell (Edge × Edge) Edge) :
    put (put cells handle first) handle second = put cells handle second := by
  funext other
  by_cases same : other = handle <;> simp [put, same]

private theorem miss_order [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (pair : Edge × Edge) (pending : List Nat) (before after : Wrapper width) (result : Edge)
    (missing : before.memo.table (key pair) = none) (done : run fuel (.call pair pending) before = .done result after) :
    ∃ rest, run rest (.order before.memo.next pair pending) {before with memo := started pair before.memo} = .done result after := by
  let published := (FlatMemoThunk.lookupOrInsert (key pair) pair before.memo).2
  have stored : published.cells before.memo.next = some ⟨pair, .suspended⟩ :=
    (FlatMemoThunk.lookup_miss (key pair) pair before.memo missing).2.2
  have running : FlatMemoThunk.setStatus before.memo.next .evaluating published = started pair before.memo := by
    simp only [FlatMemoThunk.setStatus, stored]
    simp only [published, FlatMemoThunk.lookupOrInsert, missing, started, overwrite_cells]
  have looked : advance (.call pair pending) before = .yielded (.demand before.memo.next pending) {before with memo := published} := by
    change SourceCurrentSameSymbolEdgeControl.Outcome.yielded
      (.demand (FlatMemoThunk.lookupOrInsert (key pair) pair before.memo).1 pending) {before with memo := published} = _
    exact congrArg (fun handle => SourceCurrentSameSymbolEdgeControl.Outcome.yielded (.demand handle pending)
      {before with memo := published}) (FlatMemoThunk.lookup_miss (key pair) pair before.memo missing).1
  obtain ⟨remaining, tail⟩ := tail_done fuel _ _ _ _ after result looked done
  have demanded : advance (.demand before.memo.next pending) {before with memo := published} =
      .yielded (.order before.memo.next pair pending) {before with memo := started pair before.memo} := by
    simp only [SourceCurrentSameSymbolEdgeControl.step, FlatMemoThunk.demand, stored, running]
  exact tail_done remaining _ _ _ _ after result demanded tail

private theorem ready_cell (memo : Memo)
    (valid : FlatMemoThunk.Valid (fun pair target => key pair = target) (fun _ => True) memo)
    (returned : ∀ handle cell, memo.cells handle = some cell → ∃ value, cell.status = .returned value)
    (target : Nat × Nat) (handle : Nat) (present : memo.table target = some handle) :
    ∃ pair value, memo.cells handle = some ⟨pair, .returned value⟩ := by
  obtain ⟨⟨pair, status⟩, stored, _⟩ := valid.linked target handle present
  obtain ⟨value, rfl⟩ := returned handle _ stored
  exact ⟨pair, value, stored⟩

private theorem finish_started (pair : Edge × Edge) (value : Edge) (memo : Memo) :
    FlatMemoThunk.finish memo.next value (started pair memo) = written pair value memo := by
  have stored : (started pair memo).cells memo.next = some ⟨pair, .evaluating⟩ := by simp [started, put]
  simp only [FlatMemoThunk.finish, stored]
  simp only [FlatMemoThunk.setStatus, stored]
  simp only [started, written, overwrite_cells]

private theorem finish_two (left right value : Edge) (memo : Memo) :
    FlatMemoThunk.finish memo.next value (FlatMemoThunk.finish (memo.next + 1) value
      (started (right, left) (started (left, right) memo))) =
      written (right, left) value (written (left, right) value memo) := by
  have different : memo.next ≠ memo.next + 1 := by omega
  have inner : FlatMemoThunk.finish (memo.next + 1) value (started (right, left) (started (left, right) memo)) =
      written (right, left) value (started (left, right) memo) :=
    finish_started (right, left) value (started (left, right) memo)
  rw [inner]
  have stored : (written (right, left) value (started (left, right) memo)).cells memo.next =
      some ⟨(left, right), .evaluating⟩ := by
    simp only [written, started, put, ite_eq_right different, ↓reduceIte]
  simp only [FlatMemoThunk.finish, stored]
  simp only [FlatMemoThunk.setStatus, stored]
  simp only [written, started]
  congr 1
  funext handle
  by_cases first : handle = memo.next
  · subst handle; simp [put, different]
  · by_cases second : handle = memo.next + 1 <;> simp [put, first, second]

private theorem call_image [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (left right result : Edge) (before after : Wrapper width)
    (valid : FlatMemoThunk.Valid (fun pair target => key pair = target) (fun _ => True) before.memo)
    (returned : ∀ handle cell, before.memo.cells handle = some cell → ∃ value, cell.status = .returned value)
    (done : run fuel (.call (left, right) []) before = .done result after) :
    (before.memo.table (key (left, right)) ≠ none ∧ after.memo = before.memo) ∨
      (before.memo.table (key (left, right)) = none ∧
        (¬ right.entry.identity < left.entry.identity ∨ before.memo.table (key (right, left)) ≠ none) ∧
        after.memo = written (left, right) result before.memo) ∨
      (right.entry.identity < left.entry.identity ∧ before.memo.table (key (left, right)) = none ∧
        before.memo.table (key (right, left)) = none ∧
        after.memo = written (right, left) result (written (left, right) result before.memo)) := by
  cases found : before.memo.table (key (left, right)) with
  | some handle =>
      obtain ⟨pair, value, stored⟩ := ready_cell before.memo valid returned _ handle found
      have literalFound : before.memo.table (left.entry.identity, right.entry.identity) = some handle := found
      have looked : advance (.call (left, right) []) before = .yielded (.demand handle []) before := by
        simp only [SourceCurrentSameSymbolEdgeControl.step, FlatMemoThunk.lookupOrInsert, literalFound]
      obtain ⟨rest, tail⟩ := tail_done fuel _ _ _ _ after result looked done
      have demanded : advance (.demand handle []) before = .yielded (.ret value []) before := by
        simp only [SourceCurrentSameSymbolEdgeControl.step, FlatMemoThunk.demand_ready handle before.memo pair value stored]
      obtain ⟨rest, tail⟩ := tail_done rest _ _ _ _ after result demanded tail
      exact Or.inl ⟨by simp, by simpa only [List.foldl] using (ret_memo rest value result [] before after tail).2⟩
  | none =>
      obtain ⟨rest, tail⟩ := miss_order fuel (left, right) [] before after result found done
      let current : Wrapper width := {before with memo := started (left, right) before.memo}
      by_cases swap : right.entry.identity < left.entry.identity
      · have different : key (right, left) ≠ key (left, right) := by intro equal; have := congrArg Prod.fst equal; simp only [key] at this; omega
        have ordered : advance (.order before.memo.next (left, right) []) current =
            .yielded (.call (right, left) [before.memo.next]) current := by simp only [SourceCurrentSameSymbolEdgeControl.step, swap, ↓reduceIte]
        obtain ⟨rest, tail⟩ := tail_done rest _ _ _ _ after result ordered tail
        cases reverse : before.memo.table (key (right, left)) with
        | some handle =>
            obtain ⟨pair, value, stored⟩ := ready_cell before.memo valid returned _ handle reverse
            have fresh : handle ≠ before.memo.next := by have := valid.bounded handle _ stored; omega
            have currentStored : current.memo.cells handle = some ⟨pair, .returned value⟩ := by simpa only [current, started, put, ite_eq_right fresh] using stored
            have currentFound : current.memo.table (right.entry.identity, left.entry.identity) = some handle := by
              change current.memo.table (key (right, left)) = some handle
              simpa only [current, started, put, ite_eq_right different] using reverse
            have looked : advance (.call (right, left) [before.memo.next]) current = .yielded (.demand handle [before.memo.next]) current := by
              simp only [SourceCurrentSameSymbolEdgeControl.step, FlatMemoThunk.lookupOrInsert, currentFound]
            obtain ⟨rest, tail⟩ := tail_done rest _ _ _ _ after result looked tail
            have demanded : advance (.demand handle [before.memo.next]) current = .yielded (.ret value [before.memo.next]) current := by
              simp only [SourceCurrentSameSymbolEdgeControl.step, FlatMemoThunk.demand_ready handle current.memo pair value currentStored]
            obtain ⟨rest, tail⟩ := tail_done rest _ _ _ _ after result demanded tail
            obtain ⟨rfl, image⟩ := ret_memo rest value result _ current after tail
            exact Or.inr (Or.inl ⟨rfl, Or.inr (by simp), by simpa only [List.foldl, current, finish_started] using image⟩)
        | none =>
            have missing : current.memo.table (key (right, left)) = none := by simpa only [current, started, put, ite_eq_right different] using reverse
            obtain ⟨rest, tail⟩ := miss_order rest (right, left) [before.memo.next] current after result missing tail
            let next : Wrapper width := {current with memo := started (right, left) current.memo}
            have forward : ¬ left.entry.identity < right.entry.identity := by omega
            have ordered : advance (.order current.memo.next (right, left) [before.memo.next]) next =
                .yielded (.native (.edgeBody ⟨IntersectionEmptyDomain.emptyDomain, right, left⟩ .pure) [current.memo.next, before.memo.next]) next := by
              simp only [SourceCurrentSameSymbolEdgeControl.step, forward, ↓reduceIte]
            obtain ⟨rest, tail⟩ := tail_done rest _ _ _ _ after result ordered tail
            have image := native_memo rest _ _ next after result tail
            refine Or.inr (Or.inr ⟨swap, rfl, rfl, ?_⟩)
            calc after.memo = FlatMemoThunk.finish before.memo.next result
                    (FlatMemoThunk.finish (before.memo.next + 1) result (started (right, left) (started (left, right) before.memo))) := by
                      simpa only [List.foldl, next, current, started] using image
                 _ = written (right, left) result (written (left, right) result before.memo) := finish_two left right result before.memo
      · have ordered : advance (.order before.memo.next (left, right) []) current =
            .yielded (.native (.edgeBody ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) [before.memo.next]) current := by
          simp only [SourceCurrentSameSymbolEdgeControl.step, swap, ↓reduceIte]
        obtain ⟨rest, tail⟩ := tail_done rest _ _ _ _ after result ordered tail
        have image := native_memo rest _ _ current after result tail
        exact Or.inr (Or.inl ⟨rfl, Or.inl swap, by simpa only [List.foldl, current, finish_started] using image⟩)

private theorem written_fields (pair : Edge × Edge) (value : Edge) (memo : Memo)
    (good : FlatMemoThunk.Cell (Edge × Edge) Edge → Prop)
    (valid : FlatMemoThunk.Valid (fun pair target => key pair = target) good memo)
    (returned : ∀ handle cell, memo.cells handle = some cell → ∃ value, cell.status = .returned value)
    (missing : memo.table (key pair) = none) (suspended : good ⟨pair, .suspended⟩)
    (finished : good ⟨pair, .returned value⟩) :
    FlatMemoThunk.Valid (fun pair target => key pair = target) good (written pair value memo) ∧
      (∀ handle cell, (written pair value memo).cells handle = some cell → ∃ value, cell.status = .returned value) ∧
      Extends memo.table (written pair value memo).table ∧ FlatMemoThunk.Returned memo (written pair value memo) := by
  let published := (FlatMemoThunk.lookupOrInsert (key pair) pair memo).2
  have publishedValid := FlatMemoThunk.lookup_valid (key pair) pair memo _ good valid rfl suspended
  have stored : published.cells memo.next = some ⟨pair, .suspended⟩ :=
    (FlatMemoThunk.lookup_miss (key pair) pair memo missing).2.2
  have changed := FlatMemoThunk.setStatus_valid memo.next (.returned value) published _ good publishedValid _ stored finished
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [FlatMemoThunk.setStatus, stored] at changed
    simpa only [published, FlatMemoThunk.lookupOrInsert, missing, written, overwrite_cells] using changed
  · intro handle cell present
    by_cases same : handle = memo.next
    · subst handle
      have equal : (⟨pair, .returned value⟩ : FlatMemoThunk.Cell (Edge × Edge) Edge) = cell := by simpa [written, put] using present
      subst cell; exact ⟨value, rfl⟩
    · exact returned handle cell (by simpa only [written, put, ite_eq_right same] using present)
  · simpa only [written, FlatMemoThunk.lookupOrInsert, missing] using FlatMemoThunk.lookup_extends (key pair) pair memo
  · intro handle original answer present
    have different : handle ≠ memo.next := by have := valid.bounded handle _ present; omega
    simpa only [written, put, ite_eq_right different] using present

/-- Preserve the stable pair memo through the same completed comparison and native effects. -/
theorem completed_preserves [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (semanticView : View Symbol) (model : InputMeaning semanticView)
    (ranked : RankedInput semanticView model.valid) (holds : Guard → Term Symbol → Bool)
    (fuel : Nat) (left right result : Edge) (before after : Wrapper width)
    (stable : Stable semanticView model ranked holds before)
    (leftResident : EdgeResident before.checked.native.machine.heap left)
    (rightResident : EdgeResident before.checked.native.machine.heap right)
    (done : SourceCurrentSameSymbolEdgeControl.execute fuel (.call (left, right) []) before =
      .done result after)
    (growth : Extension before.checked.native.machine after.checked.native.machine)
    (resultResident : EdgeResident after.checked.native.machine.heap result)
    (resultLaw :
      let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
      SourceCurrentAllocatedNativeContextCache.EdgeLaw semanticView model ranked holds
        ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩ result) :
    Stable semanticView model ranked holds after ∧
      Cache.Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo := by
  have retained : Stable semanticView model ranked holds {before with checked := after.checked} := by
    refine ⟨?_, stable.returned, stable.canonical⟩
    apply FlatMemoThunk.Valid.map before.memo _ _ _ stable.valid
    rintro ⟨pair, status⟩ ⟨first, second, spec⟩
    refine ⟨edge_grows _ _ growth.heap _ first, edge_grows _ _ growth.heap _ second, ?_⟩
    cases status with
    | suspended | evaluating => trivial
    | returned answer => exact ⟨edge_grows _ _ growth.heap _ spec.1, spec.2⟩
  have first := edge_grows _ _ growth.heap _ leftResident
  have second := edge_grows _ _ growth.heap _ rightResident
  have structural := FlatMemoThunk.Valid.map before.memo _ _ _ stable.valid (fun _ _ => True.intro)
  have image := call_image fuel left right result before after structural stable.returned done
  change Stable semanticView model ranked holds ⟨after.checked, after.memo⟩ ∧ _
  rcases image with ⟨_, same⟩ | ⟨missing, ordered, same⟩ | ⟨swap, missing, reverse, same⟩
  · rw [same]
    exact ⟨retained, extends_refl _, FlatMemoThunk.Returned.refl _⟩
  · rw [same]
    obtain ⟨valid, returned, extension, history⟩ := written_fields (left, right) result before.memo _ retained.valid
      retained.returned missing ⟨first, second, trivial⟩ ⟨first, second, resultResident, resultLaw⟩
    refine ⟨⟨valid, returned, ?_⟩, extension, history⟩
    intro a b handle stored
    by_cases newKey : (a, b) = key (left, right)
    · rcases Prod.mk.inj newKey with ⟨rfl, rfl⟩
      by_cases swap : right.entry.identity < left.entry.identity
      · have present := ordered.resolve_left (fun denied => denied swap)
        cases found : before.memo.table (key (right, left)) with
        | none => exact False.elim (present found)
        | some canonical =>
            exact ⟨canonical, by simpa only [swap, ↓reduceIte, key] using extension _ _ found⟩
      · exact ⟨before.memo.next, by simp only [swap, ↓reduceIte, written, key, put]⟩
    · have old : before.memo.table (a, b) = some handle := by
        simpa only [written, put, ite_eq_right newKey] using stored
      obtain ⟨canonical, present⟩ := stable.canonical a b handle old
      exact ⟨canonical, extension _ _ present⟩
  · rw [same]
    obtain ⟨valid, returned, extension, history⟩ := written_fields (left, right) result before.memo _ retained.valid
      retained.returned missing ⟨first, second, trivial⟩ ⟨first, second, resultResident, resultLaw⟩
    have different : key (right, left) ≠ key (left, right) := by
      intro equal; have := congrArg Prod.fst equal; simp only [key] at this; omega
    have reverseMissing : (written (left, right) result before.memo).table (key (right, left)) = none := by
      simpa only [written, put, ite_eq_right different] using reverse
    have forward : ¬ left.entry.identity < right.entry.identity := by omega
    obtain ⟨finalValid, finalReturned, finalExtension, finalHistory⟩ :=
      written_fields (right, left) result (written (left, right) result before.memo) _ valid returned reverseMissing
        ⟨second, first, trivial⟩ (by
          refine ⟨second, first, resultResident, ?_⟩
          simpa only [swap, forward, ↓reduceIte] using resultLaw)
    have tables := extends_trans extension finalExtension
    refine ⟨⟨finalValid, finalReturned, ?_⟩, tables, history.trans finalHistory⟩
    intro a b handle stored
    by_cases reverseKey : (a, b) = key (right, left)
    · rcases Prod.mk.inj reverseKey with ⟨rfl, rfl⟩
      exact ⟨before.memo.next + 1, by simp only [forward, ↓reduceIte, written, key, put]⟩
    · by_cases originalKey : (a, b) = key (left, right)
      · rcases Prod.mk.inj originalKey with ⟨rfl, rfl⟩
        exact ⟨before.memo.next + 1, by simp only [swap, ↓reduceIte, written, key, put]⟩
      · have old : before.memo.table (a, b) = some handle := by
          simpa only [written, put, ite_eq_right reverseKey, ite_eq_right originalKey] using stored
        obtain ⟨canonical, present⟩ := stable.canonical a b handle old
        exact ⟨canonical, tables _ _ present⟩

end MicroCFTA.SourceCurrentSameSymbolEdgeStable
