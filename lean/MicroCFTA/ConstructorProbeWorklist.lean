import MicroCFTA.ConstructorProbeWitnesses

/-!
# Finite FIFO context discovery

The source keeps the last candidate for each key in one expansion, removes
keys already found, retains earlier contexts, and appends new keys in order.
-/
namespace MicroCFTA.ConstructorProbeWorklist
open Cache
variable {Key Context : Type}

/-- Read the last entry for a key, as the source Map.fromList does. -/
def latest [DecidableEq Key] : List (Key × Context) → Table Key Context
  | [] => fun _ => none
  | (key, value) :: rest => fun other =>
      match latest rest other with
      | some previous => some previous
      | none => if other = key then some value else none

/-- Every retained candidate is one of the actual source entries for its key. -/
theorem latest_member [DecidableEq Key] (pairs : List (Key × Context)) (key : Key) (value : Context)
    (stored : latest pairs key = some value) : (key, value) ∈ pairs := by
  induction pairs with
  | nil => simp [latest] at stored
  | cons pair rest ih =>
      cases found : latest rest key with
      | some previous =>
          have same : previous = value := by simpa [latest, found] using stored
          subst previous
          exact List.mem_cons_of_mem _ (ih found)
      | none =>
          by_cases same : key = pair.1
          · subst key
            have equal : pair.2 = value := by simpa [latest, found] using stored
            exact List.mem_cons.mpr (Or.inl (Prod.ext rfl equal.symm))
          · simp [latest, found, same] at stored

/-- A key has a retained candidate exactly when it occurs in the source expansion. -/
theorem latest_present [DecidableEq Key] (pairs : List (Key × Context)) (key : Key) :
    (∃ value, latest pairs key = some value) ↔ ∃ value, (key, value) ∈ pairs := by
  constructor
  · rintro ⟨value, stored⟩
    exact ⟨value, latest_member pairs key value stored⟩
  · rintro ⟨value, member⟩
    induction pairs with
    | nil => simp at member
    | cons pair rest ih =>
        cases found : latest rest key with
        | some previous => exact ⟨previous, by simp [latest, found]⟩
        | none =>
            rcases List.mem_cons.mp member with same | later
            · cases same
              exact ⟨value, by simp [latest, found]⟩
            · obtain ⟨previous, present⟩ := ih later
              simp [found] at present

/-- Earlier contexts win; new keys retain their last candidate from this expansion. -/
def advance [DecidableEq Key] (found : Table Key Context) (pairs : List (Key × Context)) : Table Key Context :=
  fun key => match found key with
    | some value => some value
    | none => latest pairs key

/-- Compute the actual sorted keys after removing all previously found states. -/
def fresh (found : Table (Fin count) Context) (pairs : List (Fin count × Context)) : List (Fin count) :=
  (List.finRange count).filter fun key => (found key).isNone && (latest pairs key).isSome

/-- The fresh queue keys are exactly the new candidate keys. -/
theorem fresh_exact (found : Table (Fin count) Context) (pairs : List (Fin count × Context)) (key : Fin count) :
    key ∈ fresh found pairs ↔ found key = none ∧ ∃ value, latest pairs key = some value := by
  simp [fresh, Option.isSome_iff_exists]

/-- Every expansion retains all earlier complete contexts. -/
theorem advance_grows [DecidableEq Key] (found : Table Key Context) (pairs : List (Key × Context)) :
    Extends found (advance found pairs) := by
  intro key value stored
  simp [advance, stored]

/-- Every candidate key is present after its expansion. -/
theorem advance_present [DecidableEq Key] (found : Table Key Context) (pairs : List (Key × Context))
    (key : Key) (value : Context) (member : (key, value) ∈ pairs) : ∃ result, advance found pairs key = some result := by
  cases old : found key with
  | some result => exact ⟨result, by simp [advance, old]⟩
  | none => simpa [advance, old] using (latest_present pairs key).mpr ⟨value, member⟩

/-- The source finite map size counts its occupied keys. -/
def occupied (found : Table (Fin count) Context) : Nat :=
  (List.finRange count).countP fun key => (found key).isSome

/-- No fresh keys means the entire context map is unchanged. -/
theorem advance_unchanged (found : Table (Fin count) Context) (pairs : List (Fin count × Context))
    (noneFresh : fresh found pairs = []) : advance found pairs = found := by
  funext key
  cases old : found key with
  | some value => simp [advance, old]
  | none =>
      cases candidate : latest pairs key with
      | none => simp [advance, old, candidate]
      | some value =>
          have member := (fresh_exact found pairs key).mpr ⟨old, value, candidate⟩
          simp [noneFresh] at member

/-- A nonempty fresh queue strictly increases the number of stored states. -/
theorem advance_increases (found : Table (Fin count) Context) (pairs : List (Fin count × Context))
    (nonempty : fresh found pairs ≠ []) : occupied found < occupied (advance found pairs) := by
  apply Productivity.count_strict
  · intro key _ known
    obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp known
    exact Option.isSome_iff_exists.mpr ⟨value, advance_grows found pairs key value present⟩
  · obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨old, value, candidate⟩ := (fresh_exact found pairs key).mp member
    exact ⟨key, List.mem_finRange key, by simp [old], by simp [advance, old, candidate]⟩

/-- One local transition extends the stored context without changing its target state. -/
abbrev Steps (Key Context : Type) := Key → List (Key × (Context → Context))

/-- Apply each local context extension in original row and child-position order. -/
def candidates (steps : Steps Key Context) (state : Key) (context : Context) : List (Key × Context) :=
  (steps state).map fun (child, extend) => (child, extend context)

/-- Follow the source FIFO schedule until no state remains to expand. -/
def reach (steps : Steps (Fin count) Context) (found : Table (Fin count) Context) (pending : List (Fin count)) :
    Table (Fin count) Context :=
  match pending with
  | [] => found
  | state :: rest =>
      match found state with
      | none => reach steps found rest
      | some context =>
          let pairs := candidates steps state context
          reach steps (advance found pairs) (rest ++ fresh found pairs)
termination_by (count - occupied found, pending.length)
decreasing_by
  · apply Prod.Lex.right
    simp
  · by_cases noneFresh : fresh found (candidates steps state context) = []
    · have unchanged := advance_unchanged found (candidates steps state context) noneFresh
      simp only [unchanged, noneFresh, List.append_nil]
      apply Prod.Lex.right
      simp
    · apply Prod.Lex.left
      have strict := advance_increases found (candidates steps state context) noneFresh
      have bound : occupied (advance found (candidates steps state context)) ≤ count := by
        simpa [occupied] using List.countP_le_length
          (p := fun key => (advance found (candidates steps state context) key).isSome) (l := List.finRange count)
      omega

/-- Every completed context survives the actual finite FIFO traversal. -/
theorem reach_grows (steps : Steps (Fin count) Context) (found : Table (Fin count) Context) (pending : List (Fin count)) :
    Extends found (reach steps found pending) := by
  induction found, pending using reach.induct steps with
  | case1 found => simpa only [reach] using extends_refl found
  | case2 found state rest absent ih => simpa only [reach, absent] using ih
  | case3 found state rest context present pairs ih =>
      simpa only [reach, present] using extends_trans (advance_grows found pairs) ih

/-- A context property is checked separately for each concrete local extension. -/
def Preserves (steps : Steps Key Context) (property : Key → Context → Prop) : Prop :=
  ∀ state context, property state context → ∀ entry ∈ steps state, property entry.1 (entry.2 context)

/-- Candidate insertion derives its property from the actual selected entry. -/
theorem advance_property [DecidableEq Key] (steps : Steps Key Context) (property : Key → Context → Prop)
    (preserves : Preserves steps property) (found : Table Key Context)
    (sound : ∀ key value, found key = some value → property key value)
    (state : Key) (context : Context) (present : found state = some context) :
    ∀ key value, advance found (candidates steps state context) key = some value → property key value := by
  intro key value stored
  cases old : found key with
  | some previous =>
      have same : previous = value := by simpa [advance, old] using stored
      subst previous
      exact sound key value old
  | none =>
      have member := latest_member (candidates steps state context) key value (by simpa [advance, old] using stored)
      obtain ⟨entry, listed, same⟩ := List.mem_map.mp member
      cases same
      exact preserves state context (sound state context present) entry listed

/-- Local context construction preserves its semantic property through the complete worklist. -/
theorem reach_property (steps : Steps (Fin count) Context) (property : Fin count → Context → Prop)
    (preserves : Preserves steps property) (found : Table (Fin count) Context) (pending : List (Fin count))
    (sound : ∀ key value, found key = some value → property key value) :
    ∀ key value, reach steps found pending key = some value → property key value := by
  induction found, pending using reach.induct steps with
  | case1 found => simpa only [reach] using sound
  | case2 found state rest absent ih => simpa only [reach, absent] using ih sound
  | case3 found state rest context present pairs ih =>
      simpa only [reach, present] using ih (advance_property steps property preserves found sound state context present)

/-- Every found state is pending or all its outgoing candidate states are already found. -/
def Ready (steps : Steps Key Context) (found : Table Key Context) (pending : List Key) : Prop :=
  ∀ state context, found state = some context → state ∈ pending ∨
    ∀ entry ∈ steps state, ∃ value, found entry.1 = some value

/-- Expanding a present state establishes closure for that state and queues exactly its new children. -/
theorem advance_ready (steps : Steps (Fin count) Context) (found : Table (Fin count) Context)
    (state : Fin count) (context : Context) (rest : List (Fin count))
    (ready : Ready steps found (state :: rest)) :
    Ready steps (advance found (candidates steps state context)) (rest ++ fresh found (candidates steps state context)) := by
  intro key value stored
  cases old : found key with
  | some previous =>
      rcases ready key previous old with queued | closed
      · rcases List.mem_cons.mp queued with same | later
        · subst key
          right
          intro entry member
          exact advance_present found _ entry.1 (entry.2 context) (List.mem_map.mpr ⟨entry, member, rfl⟩)
        · exact Or.inl (List.mem_append_left _ later)
      · right
        intro entry member
        obtain ⟨result, present⟩ := closed entry member
        exact ⟨result, advance_grows found _ _ _ present⟩
  | none =>
      left
      apply List.mem_append_right
      exact (fresh_exact found _ key).mpr ⟨old, value, by simpa [advance, old] using stored⟩

/-- The completed FIFO traversal closes every discovered state under actual candidate transitions. -/
theorem reach_closed (steps : Steps (Fin count) Context) (found : Table (Fin count) Context)
    (pending : List (Fin count)) (ready : Ready steps found pending) :
    ∀ state context, reach steps found pending state = some context →
      ∀ entry ∈ steps state, ∃ value, reach steps found pending entry.1 = some value := by
  induction found, pending using reach.induct steps with
  | case1 found =>
      simp only [reach]
      intro state context present
      exact (ready state context present).resolve_left (by simp)
  | case2 found state rest absent ih =>
      have later : Ready steps found rest := by
        intro key value present
        rcases ready key value present with queued | closed
        · left
          rcases List.mem_cons.mp queued with same | member
          · subst key; simp [absent] at present
          · exact member
        · exact Or.inr closed
      simpa only [reach, absent] using ih later
  | case3 found state rest context present pairs ih =>
      simpa only [reach, present] using ih (advance_ready steps found state context rest ready)

/-- Every pending state has a context for the source's partial map lookup. -/
def Pending (found : Table Key Context) (queue : List Key) : Prop :=
  ∀ key ∈ queue, ∃ context, found key = some context

/-- Old pending states and every freshly appended key have actual context records. -/
theorem advance_pending (found : Table (Fin count) Context) (pairs : List (Fin count × Context))
    (rest : List (Fin count)) (present : Pending found rest) :
    Pending (advance found pairs) (rest ++ fresh found pairs) := by
  intro key member
  rcases List.mem_append.mp member with earlier | added
  · obtain ⟨context, stored⟩ := present key earlier
    exact ⟨context, advance_grows found pairs key context stored⟩
  · obtain ⟨old, context, candidate⟩ := (fresh_exact found pairs key).mp added
    exact ⟨context, by simp [advance, old, candidate]⟩

/-- This execution relation has exactly the source branches and no missing-map fallback. -/
inductive Runs (steps : Steps (Fin count) Context) :
    Table (Fin count) Context → List (Fin count) → Table (Fin count) Context → Prop where
  | done : Runs steps found [] found
  | step (present : found state = some context)
      (tail : Runs steps (advance found (candidates steps state context))
        (rest ++ fresh found (candidates steps state context)) final) : Runs steps found (state :: rest) final

/-- The total finite traversal follows the source partial-lookup execution on every valid queue. -/
theorem reach_runs (steps : Steps (Fin count) Context) (found : Table (Fin count) Context)
    (queue : List (Fin count)) (present : Pending found queue) : Runs steps found queue (reach steps found queue) := by
  induction found, queue using reach.induct steps with
  | case1 found => simpa only [reach] using (Runs.done (steps := steps) (found := found))
  | case2 found state rest absent ih =>
      obtain ⟨context, stored⟩ := present state (by simp)
      simp [absent] at stored
  | case3 found state rest context stored pairs ih =>
      have later := ih (advance_pending found pairs rest (fun key member => present key (by simp [member])))
      simpa only [reach, stored] using Runs.step stored later

end MicroCFTA.ConstructorProbeWorklist
