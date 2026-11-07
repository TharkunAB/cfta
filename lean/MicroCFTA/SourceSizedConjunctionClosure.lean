import MicroCFTA.SourceSizedConjunctionWorklist
import MicroCFTA.SourceSizedStructuralKeys

/-!
# Structural closure of completed conjunction exploration

A frontier retains the root and every stored transition child either in
the stored map or in the pending list. It also retains nonempty keys. The
literal source step preserves these facts. A ready result has no pending
keys, so its root and every child are stored.

Successful preparation derives the finite table's root and child closure.
It does not require closure of the classified original input. The current
structural FTA validator therefore accepts the returned table, including
tables whose symbols occur at more than one arity.
-/
namespace MicroCFTA.SourceSizedConjunctionClosure
open SourceSizedDecided SourceSizedConjunctionWorklist

variable {State Symbol : Type}

/-- The root and all stored children remain either stored or pending. -/
structure Frontier (seed : List State) (table : Stored State Symbol)
    (pending : List (List State)) : Prop where
  seedPresent : seed ∈ table.map Prod.fst ∨ seed ∈ pending
  childrenQueued : ∀ entry ∈ table, ∀ row ∈ entry.2, ∀ child ∈ row.children,
    child ∈ table.map Prod.fst ∨ child ∈ pending
  storedNonempty : ∀ key ∈ table.map Prod.fst, key ≠ []
  pendingNonempty : ∀ key ∈ pending, key ≠ []

/-- A finished table contains the root, has nonempty keys, and has no dangling children. -/
structure Complete (seed : List State) (table : Stored State Symbol) : Prop where
  rootPresent : seed ∈ table.map Prod.fst
  keysNonempty : ∀ key ∈ table.map Prod.fst, key ≠ []
  childClosed : ∀ entry ∈ table, ∀ row ∈ entry.2, ∀ child ∈ row.children,
    child ∈ table.map Prod.fst

/-- The literal empty-map and singleton-root initialization supplies the frontier. -/
theorem empty_frontier (root : State) : Frontier [root] ([] : Stored State Symbol) [[root]] := by
  constructor
  · exact .inr (by simp)
  · intro entry member; cases member
  · intro key member; cases member
  · intro key member
    have same : key = [root] := List.mem_singleton.mp member
    subst key
    exact List.cons_ne_nil _ _

private theorem skip_frontier (seed key : List State) (table : Stored State Symbol)
    (pending : List (List State)) (frontier : Frontier seed table (key :: pending))
    (visited : key ∈ table.map Prod.fst) : Frontier seed table pending := by
  have retained : ∀ value, value ∈ table.map Prod.fst ∨ value ∈ key :: pending →
      value ∈ table.map Prod.fst ∨ value ∈ pending := by
    intro value present
    rcases present with stored | queued
    · exact .inl stored
    · rcases List.mem_cons.mp queued with rfl | later
      · exact .inl visited
      · exact .inr later
  constructor
  · exact retained seed frontier.seedPresent
  · intro entry entryIn row rowIn child childIn
    exact retained child (frontier.childrenQueued entry entryIn row rowIn child childIn)
  · exact frontier.storedNonempty
  · intro key present
    exact frontier.pendingNonempty key (List.mem_cons_of_mem _ present)

private theorem insert_frontier (seed key : List State) (table : Stored State Symbol)
    (pending : List (List State)) (rows : List (Row (List State) Symbol (List (List Nat))))
    (frontier : Frontier seed table (key :: pending))
    (nonempty : ∀ row ∈ rows, ∀ child ∈ row.children, child ≠ []) :
    Frontier seed ((key, rows) :: table) ((rows.flatMap fun row => row.children) ++ pending) := by
  have retained : ∀ value, value ∈ table.map Prod.fst ∨ value ∈ key :: pending →
      value ∈ (((key, rows) :: table).map Prod.fst) ∨
        value ∈ (rows.flatMap fun row => row.children) ++ pending := by
    intro value present
    rcases present with stored | queued
    · exact .inl (List.mem_cons_of_mem _ stored)
    · rcases List.mem_cons.mp queued with rfl | later
      · exact .inl (by simp)
      · exact .inr (List.mem_append.mpr (.inr later))
  constructor
  · exact retained seed frontier.seedPresent
  · intro entry entryIn row rowIn child childIn
    rcases List.mem_cons.mp entryIn with rfl | previous
    · exact .inr (List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨row, rowIn, childIn⟩)))
    · exact retained child (frontier.childrenQueued entry previous row rowIn child childIn)
  · intro owner ownerIn
    change owner ∈ key :: table.map Prod.fst at ownerIn
    rcases List.mem_cons.mp ownerIn with rfl | previous
    · exact frontier.pendingNonempty owner (by simp)
    · exact frontier.storedNonempty owner previous
  · intro owner ownerIn
    rcases List.mem_append.mp ownerIn with scheduled | previous
    · obtain ⟨row, rowIn, childIn⟩ := List.mem_flatMap.mp scheduled
      exact nonempty row rowIn owner childIn
    · exact frontier.pendingNonempty owner (List.mem_cons_of_mem _ previous)

/-- Only an empty pending list returns ready, and it returns the current whole table. -/
theorem step_ready [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table returned : Stored State Symbol)
    (pending : List (List State)) (checked : step limit classified table pending = .ready returned) :
    pending = [] ∧ returned = table := by
  cases pending with
  | nil => exact ⟨rfl, (Action.ready.inj checked).symm⟩
  | cons key pending =>
      simp only [step] at checked
      split at checked
      · cases checked
      · split at checked
        · cases checked
        · split at checked <;> cases checked

/-- The actual skipped or inserted worklist step preserves root, child, and nonempty-key facts. -/
theorem step_frontier [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (seed : List State)
    (table nextTable : Stored State Symbol) (pending nextPending : List (List State))
    (frontier : Frontier seed table pending)
    (checked : step limit classified table pending = .next nextTable nextPending) :
    Frontier seed nextTable nextPending := by
  cases pending with
  | nil => cases checked
  | cons key pending =>
      simp only [step] at checked
      split at checked
      · rename_i visited
        rcases Action.next.inj checked with ⟨rfl, rfl⟩
        exact skip_frontier seed key table pending frontier visited
      · split at checked
        · cases checked
        · split at checked
          · cases checked
          · rcases Action.next.inj checked with ⟨rfl, rfl⟩
            apply insert_frontier seed key table pending (cappedRows limit classified key) frontier
            intro row rowIn child childIn
            exact SourceSizedConjunctionRows.rows_nonempty (SourceSizedFiniteKeys.lookup classified)
              key row (List.mem_of_mem_take rowIn) child childIn

/-- An empty pending list turns frontier facts into complete structural closure. -/
theorem frontier_finished (seed : List State) (table : Stored State Symbol)
    (frontier : Frontier seed table []) : Complete seed table := by
  constructor
  · rcases frontier.seedPresent with stored | queued
    · exact stored
    · cases queued
  · exact frontier.storedNonempty
  · intro entry entryIn row rowIn child childIn
    rcases frontier.childrenQueued entry entryIn row rowIn child childIn with stored | queued
    · exact stored
    · cases queued

private def ReadyComplete (seed : List State) : Outcome State Symbol → Prop
  | .ready table => Complete seed table
  | _ => True

private theorem evaluation_complete [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (seed : List State)
    (table : Stored State Symbol) (pending : List (List State)) (calls : Nat) (result : Outcome State Symbol)
    (execution : Evaluation limit classified table pending calls result) :
    Frontier seed table pending → ReadyComplete seed result := by
  induction execution with
  | ready checked =>
      intro frontier
      obtain ⟨empty, same⟩ := step_ready limit classified _ _ _ checked
      rw [same]
      exact frontier_finished seed _ (by simpa only [empty] using frontier)
  | limitExceeded _ => intro _; trivial
  | next checked _ ih =>
      intro frontier
      exact ih (step_frontier limit classified seed _ _ _ _ frontier checked)

/-- A concrete successful source trace discharges all stored-or-pending obligations. -/
theorem evaluation_ready [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (seed : List State)
    {table : Stored State Symbol} {pending : List (List State)} {calls : Nat}
    {result : Outcome State Symbol} {returned : Stored State Symbol}
    (execution : Evaluation limit classified table pending calls result)
    (frontier : Frontier seed table pending) (success : result = .ready returned) : Complete seed returned := by
  have completed := evaluation_complete limit classified seed table pending calls result execution frontier
  rw [success] at completed
  exact completed

/-- Successful public exploration derives root presence, nonempty keys, and child closure. -/
theorem explore_complete [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : explore limit classified root = .ready returned) : Complete [root] returned := by
  obtain ⟨_, _, execution⟩ := explore_evaluates limit classified root
  exact evaluation_ready limit classified [root] execution (empty_frontier root) success

/-- Successful source-sized preparation derives closure without original-input closure premises. -/
theorem prepare_complete [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) : Complete [root] returned :=
  explore_complete 1024 classified root returned success

/-- The returned finite map declares the initial singleton conjunction key. -/
theorem prepare_root [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) : [root] ∈ returned.map Prod.fst :=
  (prepare_complete classified root returned success).rootPresent

/-- All declared keys of a returned map contain at least one original state. -/
theorem prepare_nonempty [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) : ∀ key ∈ returned.map Prod.fst, key ≠ [] :=
  (prepare_complete classified root returned success).keysNonempty

/-- Literal entry closure implies the finite-key adapter's merged-lookup closure. -/
theorem Complete.closed [DecidableEq State] [Ord (List State)]
    (seed : List State) (table : Stored State Symbol) (complete : Complete seed table) :
    SourceSizedFiniteKeys.Closed table := by
  intro owner row member child childIn
  unfold SourceSizedFiniteKeys.lookup at member
  obtain ⟨entry, entryIn, selected⟩ := List.mem_flatMap.mp member
  have rowIn : row ∈ entry.2 := by
    split at selected
    · exact selected
    · cases selected
  exact (SourceDenseRows.mem_keys table child).mpr (complete.childClosed entry entryIn row rowIn child childIn)

/-- Successful preparation supplies finite-key closure for the actual returned map. -/
theorem prepare_closed [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) : SourceSizedFiniteKeys.Closed returned :=
  Complete.closed [root] returned (prepare_complete classified root returned success)

/-- Canonical Map.keys readback contains the returned root key. -/
theorem prepare_root_keys [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) : [root] ∈ SourceDenseRows.keys returned :=
  (SourceDenseRows.mem_keys returned [root]).mpr (prepare_root classified root returned success)

/-- Canonical Map.keys readback retains nonempty conjunction keys. -/
theorem prepare_keys_nonempty [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) : ∀ key ∈ SourceDenseRows.keys returned, key ≠ [] := by
  intro key member
  exact prepare_nonempty classified root returned success key ((SourceDenseRows.mem_keys returned key).mp member)

/-- Current structural validation accepts the computed table without a global symbol-arity premise. -/
theorem prepare_validation [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) :
    SourceFTAValidation.validateRows [root] (SourceSizedFiniteKeys.interpreted returned (fun _ _ => true)) =
      .ok (SourceSizedFiniteKeys.interpreted returned (fun _ _ => true)) :=
  SourceSizedStructuralKeys.validation_of_closed returned [root]
    (prepare_root_keys classified root returned success) (prepare_closed classified root returned success)

/-- The current public FTA builder succeeds on the whole computed table. -/
theorem prepare_mkFTA [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) :
    SourceFTAValidation.mkFTA [root] (SourceSizedFiniteKeys.interpreted returned (fun _ _ => true)) =
      .ok (FTAValidation.normalizeRows (SourceSizedFiniteKeys.interpreted returned (fun _ _ => true))) := by
  apply (SourceFTAValidation.mkFTA_exact [root] _).mpr
  exact (SourceFTAValidation.validateRows_exact [root] _).mp (prepare_validation classified root returned success)

end MicroCFTA.SourceSizedConjunctionClosure
