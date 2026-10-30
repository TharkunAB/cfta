import MicroCFTA.SourcePruningNarrowLineage
import MicroCFTA.SourcePruningNarrowReturnedControl
import Std.Tactic

/-!
# A finite bound for consecutive actual changed row filters

The carrier contains complete edges from one preserved row source.
Keys and fuel can vary at each observed step. A first actual closed filter
supplies the physical normal form. Source resets need a separate bound.

-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Key : Type}

/-- Count carrier occurrences whose complete edge occurs in the current root rows. -/
noncomputable def rootRowCount (carrier : List (EdgeValue Symbol Guard))
    (value : Value Symbol Guard) : Nat :=
  match carrier with
  | [] => 0
  | edge :: rest => by
      classical
      exact if edge ∈ nodeEdges value then rootRowCount rest value + 1 else rootRowCount rest value

private theorem rootRowCount_le_length (carrier : List (EdgeValue Symbol Guard))
    (value : Value Symbol Guard) : rootRowCount carrier value ≤ carrier.length := by
  classical
  induction carrier with
  | nil => simp only [rootRowCount, List.length_nil, Nat.le_refl]
  | cons edge rest ih =>
      by_cases member : edge ∈ nodeEdges value
      · simp only [rootRowCount, ite_eq_left member, List.length_cons]
        omega
      · simp only [rootRowCount, ite_eq_right member, List.length_cons]
        omega

private theorem rootRowCount_mono (carrier : List (EdgeValue Symbol Guard))
    (value result : Value Symbol Guard)
    (subset : ∀ edge ∈ nodeEdges result, edge ∈ nodeEdges value) :
    rootRowCount carrier result ≤ rootRowCount carrier value := by
  classical
  induction carrier with
  | nil => simp only [rootRowCount, Nat.le_refl]
  | cons edge rest ih =>
      by_cases old : edge ∈ nodeEdges value
      · by_cases next : edge ∈ nodeEdges result
        · simp only [rootRowCount, ite_eq_left old, ite_eq_left next]
          omega
        · simp only [rootRowCount, ite_eq_left old, ite_eq_right next]
          omega
      · have next : edge ∉ nodeEdges result := fun member => old (subset edge member)
        simpa only [rootRowCount, ite_eq_right old, ite_eq_right next] using ih

private theorem rootRowCount_strict (carrier : List (EdgeValue Symbol Guard))
    (value result : Value Symbol Guard)
    (subset : ∀ edge ∈ nodeEdges result, edge ∈ nodeEdges value)
    (loss : ∃ edge ∈ carrier, edge ∈ nodeEdges value ∧ edge ∉ nodeEdges result) :
    rootRowCount carrier result < rootRowCount carrier value := by
  classical
  revert loss
  induction carrier with
  | nil =>
      intro loss
      rcases loss with ⟨edge, member, _⟩
      cases member
  | cons edge rest ih =>
      intro loss
      obtain ⟨lost, member, oldLost, absentLost⟩ := loss
      rcases List.mem_cons.mp member with same | tail
      · subst lost
        have monotone := rootRowCount_mono rest value result subset
        simp only [rootRowCount, ite_eq_left oldLost, ite_eq_right absentLost]
        omega
      · have decreased := ih ⟨lost, tail, oldLost, absentLost⟩
        by_cases old : edge ∈ nodeEdges value
        · by_cases next : edge ∈ nodeEdges result
          · simp only [rootRowCount, ite_eq_left old, ite_eq_left next]
            omega
          · simp only [rootRowCount, ite_eq_left old, ite_eq_right next]
            omega
        · have next : edge ∉ nodeEdges result := fun retained => old (subset edge retained)
          simpa only [rootRowCount, ite_eq_right old, ite_eq_right next] using decreased

/-- An actual changed ordinary filter strictly decreases complete-edge carrier membership. -/
theorem narrowAt_changed_rootRowCount_lt [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (oldHandle newHandle : Nat) (carrier : List (EdgeValue Symbol Guard))
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (normal : EqualityOrdinaryReadback.Normal before value)
    (included : ∀ edge ∈ nodeEdges value, edge ∈ carrier)
    (returned : narrowAt fits admits fuel key value before = .done result after)
    (oldEncoded : SourcePruningEnumerationNodes.encodeNode value = some oldHandle)
    (newEncoded : SourcePruningEnumerationNodes.encodeNode result = some newHandle)
    (changed : newHandle ≠ oldHandle) :
    rootRowCount carrier result < rootRowCount carrier value ∧
      (∀ edge ∈ nodeEdges result, edge ∈ carrier) := by
  obtain ⟨subset, lost, member, absent⟩ := narrowAt_changed_loses_row fits admits fuel key
    value result before after oldHandle newHandle ready available ordinary normal
    returned oldEncoded newEncoded changed
  exact ⟨rootRowCount_strict carrier value result subset ⟨lost, included lost member, member, absent⟩,
    fun edge retained => included edge (subset edge retained)⟩

/-- A finite history of consecutive actual successful filters with changed encoded handles. -/
inductive ChangedFilters [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool) :
    State Symbol Guard → Value Symbol Guard → Nat → State Symbol Guard → Value Symbol Guard → Prop
  /-- A history with no steps retains its heap and value. -/
  | nil {heap : State Symbol Guard} {value : Value Symbol Guard} :
      ChangedFilters fits admits heap value 0 heap value
  /-- Add one observed changed filter before the remaining history. -/
  | cons {before middle after : State Symbol Guard} {value next result : Value Symbol Guard} {count : Nat}
      (fuel : Nat) (key : Key) (oldHandle newHandle : Nat)
      (returned : narrowAt fits admits fuel key value before = .done next middle)
      (oldEncoded : SourcePruningEnumerationNodes.encodeNode value = some oldHandle)
      (newEncoded : SourcePruningEnumerationNodes.encodeNode next = some newHandle)
      (changed : newHandle ≠ oldHandle)
      (rest : ChangedFilters fits admits middle next count after result) :
      ChangedFilters fits admits before value (count + 1) after result

/-- A changed-filter history consumes at most the complete-edge membership of its fixed carrier. -/
theorem ChangedFilters.rootRowCount_bound [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (before after : State Symbol Guard) (value result : Value Symbol Guard) (count : Nat)
    (history : ChangedFilters fits admits before value count after result)
    (carrier : List (EdgeValue Symbol Guard))
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (normal : EqualityOrdinaryReadback.Normal before value)
    (included : ∀ edge ∈ nodeEdges value, edge ∈ carrier) :
    count + rootRowCount carrier result ≤ rootRowCount carrier value ∧
      (∀ edge ∈ nodeEdges result, edge ∈ carrier) := by
  revert ready available closed ordinary normal included
  induction history with
  | nil =>
      intro ready available closed ordinary normal included
      exact ⟨by omega, included⟩
  | @cons before middle after value next result count fuel key oldHandle newHandle
      returned oldEncoded newEncoded changed rest ih =>
      intro ready available closed ordinary normal included
      obtain ⟨decreased, nextIncluded⟩ := narrowAt_changed_rootRowCount_lt fits admits fuel key
        value next before middle oldHandle newHandle carrier ready available ordinary normal
        included returned oldEncoded newEncoded changed
      obtain ⟨kept, nextAvailable, nextClosed, nextOrdinary, nextNormal, _, _⟩ :=
        narrowAt_returned_control fits admits fuel key value next before middle ready available closed returned
      obtain ⟨remaining, finalIncluded⟩ := ih kept.ready nextAvailable nextClosed nextOrdinary nextNormal nextIncluded
      exact ⟨by omega, finalIncluded⟩

/-- A first actual closed filter supplies Normal and bounds all later consecutive changed filters. -/
theorem changedFilters_after_returned_bound [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (initial value result : Value Symbol Guard)
    (before middle after : State Symbol Guard) (count : Nat)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before initial) (closed : initial.free = [])
    (returned : narrowAt fits admits fuel key initial before = .done value middle)
    (history : ChangedFilters fits admits middle value count after result) :
    count ≤ (nodeEdges value).length := by
  obtain ⟨kept, currentAvailable, currentClosed, currentOrdinary, currentNormal, _, _⟩ :=
    narrowAt_returned_control fits admits fuel key initial value before middle ready available closed returned
  have bounded := ChangedFilters.rootRowCount_bound fits admits middle after value result count history
    (nodeEdges value) kept.ready currentAvailable currentClosed currentOrdinary currentNormal
    (fun _ member => member)
  have carrierBound := rootRowCount_le_length (nodeEdges value) value
  omega

/-- An ordinary source bounds subsequent changed filters by its original root-row length. -/
theorem changedFilters_after_ordinary_returned_bound [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (initial value result : Value Symbol Guard)
    (before middle after : State Symbol Guard) (count : Nat)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before initial) (closed : initial.free = [])
    (ordinary : SourceEqualityRequiredCache.Ordinary initial)
    (returned : narrowAt fits admits fuel key initial before = .done value middle)
    (history : ChangedFilters fits admits middle value count after result) :
    count ≤ (nodeEdges initial).length := by
  have rows := narrowAt_ordinary_rows fits admits fuel key initial value before middle
    ready available ordinary returned
  obtain ⟨kept, currentAvailable, currentClosed, currentOrdinary, currentNormal, _, _⟩ :=
    narrowAt_returned_control fits admits fuel key initial value before middle ready available closed returned
  have bounded := ChangedFilters.rootRowCount_bound fits admits middle after value result count history
    (nodeEdges initial) kept.ready currentAvailable currentClosed currentOrdinary currentNormal
    (fun edge member => (rows edge member).1)
  have carrierBound := rootRowCount_le_length (nodeEdges initial) value
  omega

end MicroCFTA.SourcePruningNativeView
