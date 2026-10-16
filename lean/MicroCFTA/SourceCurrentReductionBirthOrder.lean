import MicroCFTA.GroupPositions

/-!
# Finite first births and refold birth transport

Each observed round supplies a finite list of edge keys. First insertion
retains the earlier round. Refold observations supply original and mapped
keys. Mapped collisions and the union with original births take minima.

The source traversal, refold execution, machine identities, native IntMap,
Double conversion, and enumerator order remain explicit adapters. In
particular, injective key renaming is not a process history theorem.
-/
namespace MicroCFTA.SourceCurrentReductionBirthOrder
open GroupPositions (Table insertFirst)
variable {Key Other : Type} [DecidableEq Key] [DecidableEq Other]

/-- Record one round without replacing any earlier birth. -/
def recordRound (round : Nat) : List Key → Table Key → Table Key
  | [], table => table
  | key :: rest, table => recordRound round rest (insertFirst table key round)

/-- Read successive observed rounds in source order. -/
def birthsFrom (start : Nat) : List (List Key) → Table Key → Table Key
  | [], table => table
  | keys :: rest, table => birthsFrom (start + 1) rest (recordRound start keys table)

/-- The complete source birth table starts at round zero with no entries. -/
def births (rounds : List (List Key)) : Table Key := birthsFrom 0 rounds (fun _ => none)

/-- Independently locate the first observed round containing a key. -/
def locateRound (start : Nat) : List (List Key) → Key → Option Nat
  | [], _ => none
  | keys :: rest, key => if key ∈ keys then some start else locateRound (start + 1) rest key

/-- An observed occurrence retains its literal round number. -/
def Occurs (start : Nat) : List (List Key) → Key → Nat → Prop
  | [], _, _ => False
  | keys :: rest, key, round => key ∈ keys ∧ round = start ∨ Occurs (start + 1) rest key round

/-- One source round keeps its first entry or installs this round number. -/
theorem recordRound_lookup (round : Nat) (keys : List Key) (table : Table Key) (key : Key) :
    recordRound round keys table key = if key ∈ keys then (table key).or (some round) else table key := by
  induction keys generalizing table with
  | nil => simp [recordRound]
  | cons first rest ih =>
      rw [recordRound, ih]
      by_cases same : key = first
      · subst first; cases found : table key <;> simp [insertFirst, found]
      · by_cases member : key ∈ rest <;> simp [insertFirst, same, member]

/-- The literal insertion fold returns the first existing or observed birth. -/
theorem birthsFrom_lookup (start : Nat) (rounds : List (List Key)) (table : Table Key) (key : Key) :
    birthsFrom start rounds table key = (table key).or (locateRound start rounds key) := by
  induction rounds generalizing start table with
  | nil => simp [birthsFrom, locateRound]
  | cons keys rest ih =>
      rw [birthsFrom, ih, recordRound_lookup]
      by_cases member : key ∈ keys <;> cases table key <;> simp [locateRound, member]

/-- An initially empty table has exactly the independent first-round lookup. -/
theorem births_lookup (rounds : List (List Key)) (key : Key) :
    births rounds key = locateRound 0 rounds key := by simp [births, birthsFrom_lookup]

omit [DecidableEq Key] in
/-- Every occurrence is at or after the initial round number. -/
theorem occurs_lower (start : Nat) (rounds : List (List Key)) (key : Key) (round : Nat)
    (occurs : Occurs start rounds key round) : start ≤ round := by
  induction rounds generalizing start with
  | nil => cases occurs
  | cons keys rest ih =>
      rcases occurs with ⟨_, rfl⟩ | later
      · exact Nat.le_refl _
      · have bounded := ih (start + 1) later; omega

/-- A stored first round is an actual observed occurrence. -/
theorem locateRound_origin (start : Nat) (rounds : List (List Key)) (key : Key) (round : Nat)
    (found : locateRound start rounds key = some round) : Occurs start rounds key round := by
  induction rounds generalizing start with
  | nil => cases found
  | cons keys rest ih =>
      by_cases member : key ∈ keys
      · simp only [locateRound, member, ite_true, Option.some.injEq] at found
        exact Or.inl ⟨member, found.symm⟩
      · exact Or.inr (ih (start + 1) (by simpa only [locateRound, member, ite_false] using found))

/-- Every other observed occurrence is at or after the stored first round. -/
theorem locateRound_le (start : Nat) (rounds : List (List Key)) (key : Key) (round other : Nat)
    (found : locateRound start rounds key = some round) (occurs : Occurs start rounds key other) : round ≤ other := by
  induction rounds generalizing start with
  | nil => cases found
  | cons keys rest ih =>
      by_cases member : key ∈ keys
      · simp only [locateRound, member, ite_true, Option.some.injEq] at found
        subst round
        exact occurs_lower start (keys :: rest) key other occurs
      · rcases occurs with ⟨present, _⟩ | later
        · exact False.elim (member present)
        · exact ih (start + 1) (by simpa only [locateRound, member, ite_false] using found) later

/-- A missing lookup has no observed occurrence. -/
theorem locateRound_none (start : Nat) (rounds : List (List Key)) (key : Key) :
    locateRound start rounds key = none ↔ ∀ round, ¬ Occurs start rounds key round := by
  induction rounds generalizing start with
  | nil => simp [locateRound, Occurs]
  | cons keys rest ih =>
      by_cases member : key ∈ keys
      · simp only [locateRound, member, ite_true, reduceCtorEq, false_iff]
        intro absent
        exact absent start (Or.inl ⟨member, rfl⟩)
      · simpa only [locateRound, member, ite_false, Occurs, member, false_and, false_or] using ih (start + 1)

/-- First insertion returns exactly the earliest observed birth. -/
theorem births_exact (rounds : List (List Key)) (key : Key) (round : Nat) :
    births rounds key = some round ↔ Occurs 0 rounds key round ∧
      ∀ other, Occurs 0 rounds key other → round ≤ other := by
  rw [births_lookup]
  constructor
  · intro found
    exact ⟨locateRound_origin 0 rounds key round found, fun other occurs => locateRound_le 0 rounds key round other found occurs⟩
  · rintro ⟨occurs, minimal⟩
    cases found : locateRound 0 rounds key with
    | none => exact False.elim ((locateRound_none 0 rounds key).mp found round occurs)
    | some other =>
        have first := locateRound_le 0 rounds key other round found occurs
        have second := minimal other (locateRound_origin 0 rounds key other found)
        exact congrArg some (Nat.le_antisymm first second)

/-- Every stored birth lies within the finite observed history. -/
theorem births_bound (rounds : List (List Key)) (key : Key) (round : Nat)
    (found : births rounds key = some round) : round < rounds.length := by
  have general : ∀ (rounds : List (List Key)) start round,
      locateRound start rounds key = some round → round < start + rounds.length := by
    intro history
    induction history with
    | nil => intro start round found; cases found
    | cons keys rest ih =>
        intro start round found
        by_cases member : key ∈ keys
        · simp only [locateRound, member, ite_true, Option.some.injEq] at found
          simp [← found]
        · have bounded := ih (start + 1) round (by simpa only [locateRound, member, ite_false] using found)
          simp only [List.length_cons]; omega
  simpa using general rounds 0 round (by simpa only [births_lookup] using found)

/-- Minimum union retains a value from either table and combines collisions. -/
def merge : Option Nat → Option Nat → Option Nat
  | none, right => right
  | left, none => left
  | some left, some right => some (min left right)

/-- A minimum is an originating value below both supplied values. -/
theorem merge_exact (left right : Option Nat) (round : Nat) :
    merge left right = some round ↔ (left = some round ∨ right = some round) ∧
      ∀ other, left = some other ∨ right = some other → round ≤ other := by
  cases left with
  | none => cases right <;> simp [merge] <;> omega
  | some first =>
      cases right with
      | none => simp [merge]; omega
      | some second =>
          simp only [merge, Option.some.injEq]
          constructor
          · intro same
            subst round
            refine ⟨?_, ?_⟩
            · rcases Nat.le_total first second with ordered | ordered
              · exact Or.inl (Nat.min_eq_left ordered).symm
              · exact Or.inr (Nat.min_eq_right ordered).symm
            · intro other supplied
              rcases supplied with rfl | rfl
              · exact Nat.min_le_left _ _
              · exact Nat.min_le_right _ _
          · rintro ⟨origin, least⟩
            rcases origin with rfl | rfl
            · exact Nat.min_eq_left (least second (Or.inr rfl))
            · exact Nat.min_eq_right (least first (Or.inl rfl))

/-- Fold the source minimum insertion over a finite entry list. -/
def fromMinEntries : List (Key × Nat) → Table Key
  | [], _ => none
  | (key, round) :: rest, queried =>
      merge (if queried = key then some round else none) (fromMinEntries rest queried)

/-- A minimum lookup is absent exactly when no entry supplies that key. -/
theorem fromMinEntries_none (entries : List (Key × Nat)) (key : Key) :
    fromMinEntries entries key = none ↔ ∀ round, (key, round) ∉ entries := by
  induction entries with
  | nil => simp [fromMinEntries]
  | cons entry rest ih =>
      obtain ⟨other, first⟩ := entry
      by_cases same : key = other
      · subst other
        have impossible : ¬ (∀ round, (key, round) ∉ (key, first) :: rest) :=
          fun absent => absent first List.mem_cons_self
        constructor
        · intro missing
          cases found : fromMinEntries rest key <;> simp [fromMinEntries, merge, found] at missing
        · intro absent; exact False.elim (impossible absent)
      · simpa [fromMinEntries, same, merge] using ih

/-- Every minimum comes from an actual colliding entry. -/
theorem fromMinEntries_origin (entries : List (Key × Nat)) (key : Key) (round : Nat)
    (found : fromMinEntries entries key = some round) : (key, round) ∈ entries := by
  induction entries generalizing round with
  | nil => cases found
  | cons entry rest ih =>
      obtain ⟨other, first⟩ := entry
      by_cases same : key = other
      · subst other
        have combined : merge (some first) (fromMinEntries rest key) = some round := by simpa [fromMinEntries] using found
        rcases (merge_exact _ _ _).mp combined |>.1 with atHead | later
        · cases atHead; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih round later)
      · exact List.mem_cons_of_mem _ (ih round (by simpa [fromMinEntries, same, merge] using found))

/-- A stored minimum is below every colliding entry. -/
theorem fromMinEntries_le (entries : List (Key × Nat)) (key : Key) (round other : Nat)
    (found : fromMinEntries entries key = some round) (member : (key, other) ∈ entries) : round ≤ other := by
  induction entries generalizing round with
  | nil => cases found
  | cons entry rest ih =>
      obtain ⟨entryKey, first⟩ := entry
      by_cases same : key = entryKey
      · subst entryKey
        have combined : merge (some first) (fromMinEntries rest key) = some round := by simpa [fromMinEntries] using found
        have least := ((merge_exact _ _ _).mp combined).2
        rcases List.mem_cons.mp member with atHead | later
        · have equal : other = first := (Prod.mk.inj atHead).2
          rw [equal]
          exact least first (Or.inl rfl)
        · cases stored : fromMinEntries rest key with
          | none => exact False.elim (((fromMinEntries_none rest key).mp stored other) later)
          | some value => exact Nat.le_trans (least value (Or.inr stored)) (ih value stored later)
      · have later : (key, other) ∈ rest := by simpa [same] using member
        exact ih round (by simpa [fromMinEntries, same, merge] using found) later

/-- Minimum insertion returns exactly a supplied value below all colliding entries. -/
theorem fromMinEntries_exact (entries : List (Key × Nat)) (key : Key) (round : Nat) :
    fromMinEntries entries key = some round ↔ (key, round) ∈ entries ∧
      ∀ other, (key, other) ∈ entries → round ≤ other := by
  constructor
  · intro found
    exact ⟨fromMinEntries_origin entries key round found,
      fun other member => fromMinEntries_le entries key round other found member⟩
  · rintro ⟨member, least⟩
    cases found : fromMinEntries entries key with
    | none => exact False.elim (((fromMinEntries_none entries key).mp found round) member)
    | some other =>
        have first := fromMinEntries_le entries key other round found member
        have second := least other (fromMinEntries_origin entries key other found)
        exact congrArg some (Nat.le_antisymm first second)

/-- Minimum union is absent exactly when both inputs are absent. -/
theorem merge_none (left right : Option Nat) : merge left right = none ↔ left = none ∧ right = none := by
  cases left <;> cases right <;> simp [merge]

/-- Minimum insertion associates independently of the entry traversal order. -/
theorem merge_assoc (first second third : Option Nat) :
    merge (merge first second) third = merge first (merge second third) := by
  cases first <;> cases second <;> cases third <;> simp [merge, Nat.min_assoc]

/-- Insert a colliding entry with the source minimum combiner. -/
def insertMin (table : Table Key) (key : Key) (round : Nat) : Table Key :=
  fun queried => merge (table queried) (if queried = key then some round else none)

/-- The source fromListWith operation reads entries from left to right. -/
def foldMin : List (Key × Nat) → Table Key → Table Key
  | [], table => table
  | (key, round) :: rest, table => foldMin rest (insertMin table key round)

/-- The finite minimum specification equals the actual left insertion fold. -/
theorem foldMin_lookup (entries : List (Key × Nat)) (table : Table Key) (key : Key) :
    foldMin entries table key = merge (table key) (fromMinEntries entries key) := by
  induction entries generalizing table with
  | nil => cases found : table key <;> simp [foldMin, fromMinEntries, merge, found]
  | cons entry rest ih =>
      obtain ⟨other, round⟩ := entry
      rw [foldMin, ih]
      exact merge_assoc (table key) _ _

/-- Observed refold pairs retain the original birth under the mapped edge key. -/
def transportEntries (born : Table Key) (edges : List (Key × Key)) : List (Key × Nat) :=
  edges.filterMap (fun edge => (born edge.1).map (fun round => (edge.2, round)))

omit [DecidableEq Key] in
/-- A transported entry has one actual observed preimage and its original birth. -/
theorem transportEntries_mem (born : Table Key) (edges : List (Key × Key)) (key : Key) (round : Nat) :
    (key, round) ∈ transportEntries born edges ↔ ∃ original, (original, key) ∈ edges ∧ born original = some round := by
  constructor
  · intro member
    obtain ⟨⟨original, target⟩, present, supplied⟩ := List.mem_filterMap.mp member
    cases found : born original with
    | none => simp [found] at supplied
    | some birth =>
        simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at supplied
        obtain ⟨rfl, rfl⟩ := supplied
        exact ⟨original, present, found⟩
  · rintro ⟨original, present, supplied⟩
    exact List.mem_filterMap.mpr ⟨(original, key), present, by simp [supplied]⟩

/-- The source union takes minima, including keys already in the original table. -/
def minUnion (left right : Table Key) : Table Key := fun key => merge (left key) (right key)

/-- Original births precede the mapped-entry table in the literal source union. -/
def rounds (born : Table Key) (edges : List (Key × Key)) : Table Key :=
  minUnion born (fromMinEntries (transportEntries born edges))

/-- The two source minimum operations equal insertion into the original table. -/
theorem rounds_fold (born : Table Key) (edges : List (Key × Key)) :
    rounds born edges = foldMin (transportEntries born edges) born := by
  funext key
  exact (foldMin_lookup _ born key).symm

/-- Either the key itself or one observed refold preimage supplies a birth. -/
def Supplies (born : Table Key) (edges : List (Key × Key)) (key : Key) (round : Nat) : Prop :=
  born key = some round ∨ ∃ original, (original, key) ∈ edges ∧ born original = some round

/-- The literal minimum union returns exactly the earliest original or mapped birth. -/
theorem rounds_exact (born : Table Key) (edges : List (Key × Key)) (key : Key) (round : Nat) :
    rounds born edges key = some round ↔ Supplies born edges key round ∧
      ∀ other, Supplies born edges key other → round ≤ other := by
  have forward : ∀ birth, rounds born edges key = some birth → Supplies born edges key birth ∧
      ∀ other, Supplies born edges key other → birth ≤ other := by
    intro birth found
    have exactMerge := (merge_exact (born key) (fromMinEntries (transportEntries born edges) key) birth).mp found
    refine ⟨?_, ?_⟩
    · rcases exactMerge.1 with original | mapped
      · exact Or.inl original
      · exact Or.inr ((transportEntries_mem born edges key birth).mp (fromMinEntries_origin _ key birth mapped))
    · intro other supplied
      rcases supplied with original | mapped
      · exact exactMerge.2 other (Or.inl original)
      · have member := (transportEntries_mem born edges key other).mpr mapped
        cases stored : fromMinEntries (transportEntries born edges) key with
        | none => exact False.elim (((fromMinEntries_none _ key).mp stored other) member)
        | some first =>
            exact Nat.le_trans (exactMerge.2 first (Or.inr stored))
              (fromMinEntries_le _ key first other stored member)
  constructor
  · exact forward round
  · rintro ⟨origin, least⟩
    cases found : rounds born edges key with
    | none =>
        have absent := (merge_none (born key) (fromMinEntries (transportEntries born edges) key)).mp found
        rcases origin with original | mapped
        · rw [absent.1] at original; cases original
        · exact False.elim (((fromMinEntries_none _ key).mp absent.2 round)
            ((transportEntries_mem born edges key round).mpr mapped))
    | some other =>
        have actual := forward other found
        exact congrArg some (Nat.le_antisymm (actual.2 round origin) (least other actual.1))

/-- Injective key renaming preserves the first observed round. -/
theorem locateRound_rename (rename : Key → Other) (injective : Function.Injective rename)
    (history : List (List Key)) (key : Key) (start : Nat) :
    locateRound start (history.map (List.map rename)) (rename key) = locateRound start history key := by
  induction history generalizing start with
  | nil => rfl
  | cons keys rest ih =>
      have membership : rename key ∈ keys.map rename ↔ key ∈ keys := by
        constructor
        · intro present
          obtain ⟨original, member, same⟩ := List.mem_map.mp present
          exact injective same ▸ member
        · exact fun present => List.mem_map.mpr ⟨key, present, rfl⟩
      simp only [List.map_cons, locateRound, membership, ih]

/-- A changed identity allocation preserves births under an injective correspondence. -/
theorem births_rename (rename : Key → Other) (injective : Function.Injective rename)
    (history : List (List Key)) (key : Key) :
    births (history.map (List.map rename)) (rename key) = births history key := by
  rw [births_lookup, births_lookup, locateRound_rename rename injective]

/-- Minimum collisions depend on key equality, which an injective renaming preserves. -/
theorem fromMinEntries_rename (rename : Key → Other) (injective : Function.Injective rename)
    (entries : List (Key × Nat)) (key : Key) :
    fromMinEntries (entries.map (fun entry => (rename entry.1, entry.2))) (rename key) = fromMinEntries entries key := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨other, round⟩ := entry
      have equal : rename key = rename other ↔ key = other := ⟨fun same => injective same, congrArg rename⟩
      simp only [List.map_cons, fromMinEntries, equal, ih]

omit [DecidableEq Key] [DecidableEq Other] in
/-- Observed refold transport commutes with a shared key correspondence. -/
theorem transportEntries_rename (rename : Key → Other) (born : Table Key) (renamed : Table Other)
    (same : ∀ key, renamed (rename key) = born key) (edges : List (Key × Key)) :
    transportEntries renamed (edges.map (fun edge => (rename edge.1, rename edge.2))) =
      (transportEntries born edges).map (fun entry => (rename entry.1, entry.2)) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      obtain ⟨original, target⟩ := edge
      unfold transportEntries at ih ⊢
      cases found : born original <;>
        simp only [List.map_cons, List.filterMap_cons, same original, found, Option.map_none, Option.map_some, List.map_cons]
      all_goals rw [ih]

/-- Both source minimum operations preserve injective identity correspondences. -/
theorem rounds_rename (rename : Key → Other) (injective : Function.Injective rename)
    (born : Table Key) (renamed : Table Other) (same : ∀ key, renamed (rename key) = born key)
    (edges : List (Key × Key)) (key : Key) :
    rounds renamed (edges.map (fun edge => (rename edge.1, rename edge.2))) (rename key) = rounds born edges key := by
  unfold rounds minUnion
  rw [same, transportEntries_rename rename born renamed same edges, fromMinEntries_rename rename injective]

/-- Renaming all observed rounds and refold pairs preserves the final birth lookup. -/
theorem history_rounds_rename (rename : Key → Other) (injective : Function.Injective rename)
    (history : List (List Key)) (edges : List (Key × Key)) (key : Key) :
    rounds (births (history.map (List.map rename)))
      (edges.map (fun edge => (rename edge.1, rename edge.2))) (rename key) = rounds (births history) edges key :=
  rounds_rename rename injective (births history) _ (fun key => births_rename rename injective history key) edges key

/-- Known original or transported births precede the history-length fallback. -/
theorem rounds_bound (history : List (List Key)) (edges : List (Key × Key)) (key : Key) (round : Nat)
    (found : rounds (births history) edges key = some round) : round < history.length := by
  rcases ((rounds_exact (births history) edges key round).mp found).1 with original | mapped
  · exact births_bound history key round original
  · obtain ⟨original, _, supplied⟩ := mapped
    exact births_bound history original round supplied

/-- The source fallback uses the count only when no birth is known. -/
def index (count : Nat) (table : Table Key) (key : Key) : Nat := (table key).getD count

omit [DecidableEq Key] in
/-- An unknown edge receives exactly the source fallback count. -/
theorem index_unknown (count : Nat) (table : Table Key) (key : Key) (absent : table key = none) :
    index count table key = count := by simp [index, absent]

/-- Every known birth is strictly earlier than an unknown edge's fallback. -/
theorem known_before_fallback (history : List (List Key)) (edges : List (Key × Key)) (key : Key) (round : Nat)
    (found : rounds (births history) edges key = some round) :
    index history.length (rounds (births history) edges) key < history.length := by
  simpa [index, found] using rounds_bound history edges key round found

/-- Known edges precede unknown edges in the finite birth-index order. -/
theorem known_before_unknown (history : List (List Key)) (edges : List (Key × Key)) (known unknown : Key) (round : Nat)
    (found : rounds (births history) edges known = some round) (absent : rounds (births history) edges unknown = none) :
    index history.length (rounds (births history) edges) known <
      index history.length (rounds (births history) edges) unknown := by
  rw [index_unknown history.length _ unknown absent]
  exact known_before_fallback history edges known round found

/-- The bounded reduction worker includes its input and stops on equality. -/
def reductions [DecidableEq Node] (step : Node → Node) : Nat → Node → List Node
  | 0, node => [node]
  | fuel + 1, node => if step node = node then [node] else node :: reductions step fuel (step node)

/-- A bounded reduction history has at least one and at most fuel-plus-one spaces. -/
theorem reductions_length [DecidableEq Node] (step : Node → Node) (fuel : Nat) (node : Node) :
    0 < (reductions step fuel node).length ∧ (reductions step fuel node).length ≤ fuel + 1 := by
  induction fuel generalizing node with
  | zero => simp [reductions]
  | succ fuel ih =>
      simp only [reductions]
      split
      · simp
      · have bounded := ih (step node); simp only [List.length_cons]; omega

/-- The fixed source limit bounds the normal history; public arbitrary histories need no such bound. -/
theorem source_history_bound [DecidableEq Node] (step : Node → Node) (node : Node) :
    0 < (reductions step 30 node).length ∧ (reductions step 30 node).length ≤ 31 := reductions_length step 30 node

end MicroCFTA.SourceCurrentReductionBirthOrder
