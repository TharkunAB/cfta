import MicroCFTA.SourceSizedGroupedRankComplete
import MicroCFTA.SourceSizedGroupedRankDispatch
import MicroCFTA.SourceSizedGroupedPreparedIndex

/-!
# The source bottom-up grouped position worker

Each term node computes its child position tables once. The source candidate
operation reads those tables. Ordered choice adds the preceding row counts,
and the last successful occurrence supplies the final state position.

Count and selector fields come from independently constructed finite source
observations. This is the value projection of the worker. Native map storage,
cache realization, lazy index productivity and execution costs are separate.
-/
namespace MicroCFTA.SourceSizedGroupedBottomUp
open Language RecursiveSize SizedRank SourceSizedDecided
open RecursiveJoinFields (ValueIndex)
open SourceSizedGroupedClasses (classes classOf)
open SourceSizedGroupedChainOrder (rowClass)

variable {State Symbol : Type}

/-- Read each source count and raw selector field with the request-computed bound. -/
def indexes (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat))))
    (state : State) : ValueIndex (Term Symbol) :=
  ⟨fun size => SourceSizedGroupedTableIndex.countAt known rows size state,
    fun position => (SourceSizedGroupedTableIndex.indexAt known rows position.size state).select position⟩

/-- The observed fields have the exact independent class counts and order. -/
theorem indexes_correct (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : SourceSizedGroupedTableIndex.MissingEmpty known rows) (state : State) :
    SourceSizedGroupedIndex.Correct (indexes known rows state) (fun size => classes rows size state) := by
  constructor
  · exact fun size => SourceSizedGroupedTableIndex.countAt_eq known rows missing size state
  · intro position bounded
    exact SourceSizedGroupedTableIndex.evaluate_select (position.size + 1) known rows missing
      position.size position.rank state (Nat.le_refl _) bounded

/-- Every size satisfies the same complete ordered row equation, including size zero. -/
theorem classes_equation (rows : State → List (Row State Symbol (List (List Nat))))
    (size : Nat) (state : State) :
    classes rows size state = classOf (fun child size => classes rows size child) (rows state) size := by
  cases size with
  | zero => simp [SourceSizedGroupedClasses.classes_zero, classOf, SourceSizedGroupedRecurrence.rowClass_zero]
  | succ remaining => exact SourceSizedGroupedRecurrence.classes_succ rows remaining state

/-- Compute cached child tables, source candidates and the last successful state position. -/
def positionsOf [DecidableEq Symbol] (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) : Term Symbol → State → Option Position
  | .node symbol values =>
      let tables := values.map (positionsOf known rows)
      fun state => if known state then
        SourceSizedGroupedRankDispatch.rowPosition
          (fun row => (SourceSizedGroupedIndex.rowIndex (indexes known rows) row).counts)
          (fun row => SourceSizedGroupedRankCandidates.candidate (indexes known rows) row symbol values tables)
          (rows state)
        else none

/-- Every computed source position selects the complete input term in the checked class. -/
theorem positionsOf_replay [DecidableEq Symbol] (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : SourceSizedGroupedTableIndex.MissingEmpty known rows)
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧ SourceSizedConjunctionSharing.Shared row)
    (term : Term Symbol) (state : State) (position : Position)
    (found : positionsOf known rows term state = some position) :
    (classes rows position.size state)[position.rank]? = some term := by
  induction term using Term.rec
      (motive_2 := fun values => SourceSizedGroupedRankCandidates.TablesSound
        (fun state size => classes rows size state) (values.map (positionsOf known rows)) values)
      generalizing state position with
  | node symbol values sound =>
      rw [positionsOf] at found
      dsimp only at found
      split at found
      next =>
        have replay := SourceSizedGroupedRankDispatch.rowPosition_replay
          (fun row => (SourceSizedGroupedIndex.rowIndex (indexes known rows) row).counts)
          (fun row => SourceSizedGroupedRankCandidates.candidate (indexes known rows) row symbol values
            (values.map (positionsOf known rows)))
          (fun row size => rowClass (fun state size => classes rows size state)
            row.label row.children row.constraint size)
          (.node symbol values) (rows state)
          (fun row _ size => (SourceSizedGroupedPlain.row_correct (indexes known rows) _
            (indexes_correct known rows missing) row).counts size)
          (fun row member result read => SourceSizedGroupedRankCandidates.candidate_replay
            (indexes known rows) _ (indexes_correct known rows missing) row (facts state row member).1
            symbol values _ sound result read)
          position found
        rw [classes_equation]
        exact replay
      next => cases found
  | nil => exact .nil
  | cons term terms first rest => exact .cons first rest

private theorem graph_node [DecidableEq Symbol]
    (rows : State → List (Row State Symbol (List (List Nat))))
    (state : State) (symbol : Symbol) (values : List (Term Symbol)) :
    Accepts (SourceSizedConjunctionLanguage.graph rows) state (.node symbol values) ↔
      ∃ row ∈ rows state, row.label = symbol ∧
        All₂ (Accepts (SourceSizedConjunctionLanguage.graph rows)) row.children values ∧
        SourceSizedConjunctionSemantics.holds row.constraint (.node symbol values) = true := by
  rw [accepts_node_iff]
  constructor
  · rintro ⟨edge, member, label, children, guard⟩
    obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp member
    exact ⟨row, rowIn, label, children, guard⟩
  · rintro ⟨row, member, label, children, guard⟩
    exact ⟨row.edge SourceSizedConjunctionSemantics.holds,
      List.mem_map.mpr ⟨row, member, rfl⟩, label, children, guard⟩

/-- Every term accepted by the prepared graph receives a bottom-up source position. -/
theorem positionsOf_complete [DecidableEq Symbol] (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : SourceSizedGroupedTableIndex.MissingEmpty known rows)
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧ SourceSizedConjunctionSharing.Shared row)
    (term : Term Symbol) (state : State)
    (accepted : Accepts (SourceSizedConjunctionLanguage.graph rows) state term) :
    ∃ position, positionsOf known rows term state = some position := by
  induction term using Term.rec
      (motive_2 := fun values => SourceSizedGroupedRankComplete.TablesComplete
        (Accepts (SourceSizedConjunctionLanguage.graph rows)) (values.map (positionsOf known rows)) values)
      generalizing state with
  | node symbol values complete =>
      obtain ⟨row, member, label, children, held⟩ := (graph_node rows state symbol values).mp accepted
      have classMember := (SourceSizedGroupedClasses.mem_classes_iff rows facts
        (nodeSize (.node symbol values)) state (.node symbol values)).mpr ⟨accepted, rfl⟩
      have gate : known state = true := by
        cases read : known state with
        | false => rw [missing state read] at classMember; cases classMember
        | true => rfl
      obtain ⟨inner, read⟩ := SourceSizedGroupedRankComplete.candidate_exists (indexes known rows)
        (Accepts (SourceSizedConjunctionLanguage.graph rows)) row symbol values
        (values.map (positionsOf known rows)) complete label children (by simpa only [label] using held)
      obtain ⟨position, found⟩ := SourceSizedGroupedRankDispatch.rowPosition_complete
        (fun row => (SourceSizedGroupedIndex.rowIndex (indexes known rows) row).counts)
        (fun row => SourceSizedGroupedRankCandidates.candidate (indexes known rows) row symbol values
          (values.map (positionsOf known rows))) (rows state) row member inner read
      exact ⟨position, by simpa only [positionsOf, gate, ite_true] using found⟩
  | nil => exact .nil
  | cons term terms first rest => exact .cons first rest

/-- Successful source position lookup is exactly prepared-graph acceptance. -/
theorem positionsOf_accepts [DecidableEq Symbol] (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : SourceSizedGroupedTableIndex.MissingEmpty known rows)
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧ SourceSizedConjunctionSharing.Shared row)
    (term : Term Symbol) (state : State) :
    (∃ position, positionsOf known rows term state = some position) ↔
      Accepts (SourceSizedConjunctionLanguage.graph rows) state term := by
  constructor
  · rintro ⟨position, found⟩
    have member := List.mem_of_getElem? (positionsOf_replay known rows missing facts term state position found)
    exact ((SourceSizedGroupedClasses.mem_classes_iff rows facts position.size state term).mp member).1
  · exact positionsOf_complete known rows missing facts term state

/-- Exact distinct classes give both source rank and guarded-selector inverse directions. -/
theorem positionsOf_select_iff [DecidableEq Symbol] (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : SourceSizedGroupedTableIndex.MissingEmpty known rows)
    (facts : ∀ owner row, row ∈ rows owner →
      CompactGroups.ValidClasses row.children.length row.constraint ∧ SourceSizedConjunctionSharing.Shared row)
    (unique : ∀ size state, (classes rows size state).Nodup)
    (term : Term Symbol) (state : State) (position : Position) :
    positionsOf known rows term state = some position ↔
      SourceSizedGroupedTableIndex.selectAt known rows position.size position.rank state = some term := by
  rw [SourceSizedGroupedTableIndex.selectAt_eq known rows missing]
  constructor
  · exact positionsOf_replay known rows missing facts term state position
  · intro selected
    have member := List.mem_of_getElem? selected
    obtain ⟨accepted, requestedSize⟩ :=
      (SourceSizedGroupedClasses.mem_classes_iff rows facts position.size state term).mp member
    obtain ⟨other, found⟩ := positionsOf_complete known rows missing facts term state accepted
    have replay := positionsOf_replay known rows missing facts term state other found
    have otherMember := List.mem_of_getElem? replay
    have otherSize := ((SourceSizedGroupedClasses.mem_classes_iff rows facts other.size state term).mp otherMember).2
    have sameSize : other.size = position.size := otherSize.symm.trans requestedSize
    rw [sameSize] at replay
    have sameRank : other.rank = position.rank := (unique position.size state).eq_of_getElem?_eq
      (List.getElem?_eq_some_iff.mp replay).1 (replay.trans selected.symm)
    have same : other = position := by
      cases other
      cases position
      simp_all
    simpa only [same] using found

end MicroCFTA.SourceSizedGroupedBottomUp
