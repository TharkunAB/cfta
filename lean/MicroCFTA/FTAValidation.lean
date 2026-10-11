import MicroCFTA.DistinctRank

/-!
# Explicit FTA validation

The source merges repeated rows before checking the initial state, dangling
children, and constructor arities, in that order. Maps use their functional
lookup semantics here. No term language is treated as empty because validation
fails.
-/
namespace MicroCFTA.FTAValidation
open Language DistinctRank

/-- A constructor must have one arity throughout a ranked automaton. -/
structure ArityError (Symbol : Type) where
  symbol : Symbol
  expected : Nat
  actual : Nat

/-- The map used while checking constructor arities. -/
abbrev Arities (Symbol : Type) := Symbol → Option Nat

/-- Insert a previously unseen constructor arity. -/
def insertArity [DecidableEq Symbol] (arities : Arities Symbol) (symbol : Symbol) (arity : Nat) : Arities Symbol :=
  fun other => if other = symbol then some arity else arities other

/-- The source's left-to-right arity validation loop. -/
def checkArities [DecidableEq Symbol] (arities : Arities Symbol) :
    List (Symbol × Nat) → Except (ArityError Symbol) (Arities Symbol)
  | [] => .ok arities
  | (symbol, arity) :: rest =>
    match arities symbol with
    | none => checkArities (insertArity arities symbol arity) rest
    | some expected => if expected = arity then checkArities arities rest
        else .error ⟨symbol, expected, arity⟩

/-- A total arity assignment agrees with every stored map entry. -/
def Extends (assignment : Symbol → Nat) (arities : Arities Symbol) : Prop :=
  ∀ symbol arity, arities symbol = some arity → assignment symbol = arity

/-- Every listed constructor has its assigned arity. -/
def Describes (assignment : Symbol → Nat) (entries : List (Symbol × Nat)) : Prop :=
  ∀ entry ∈ entries, assignment entry.1 = entry.2

/-- A successful validator preserves all old entries and records every new entry. -/
theorem check_sound [DecidableEq Symbol] (entries : List (Symbol × Nat))
    (before after : Arities Symbol) (success : checkArities before entries = .ok after) :
    (∀ symbol arity, before symbol = some arity → after symbol = some arity) ∧
      (∀ entry ∈ entries, after entry.1 = some entry.2) := by
  induction entries generalizing before with
  | nil =>
    have same : before = after := by simpa [checkArities] using success
    subst before
    exact ⟨fun _ _ found => found, by simp⟩
  | cons entry rest ih =>
    rcases entry with ⟨symbol, arity⟩
    cases found : before symbol with
    | none =>
      have next : checkArities (insertArity before symbol arity) rest = .ok after :=
        by simpa [checkArities, found] using success
      obtain ⟨old, tail⟩ := ih _ next
      constructor
      · intro other value present
        apply old
        by_cases same : other = symbol
        · subst other; simp [found] at present
        · simp [insertArity, same, present]
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact old symbol arity (by simp [insertArity])
        · exact tail entry member
    | some expected =>
      by_cases same : expected = arity
      · have next : checkArities before rest = .ok after := by simpa [checkArities, found, same] using success
        obtain ⟨old, tail⟩ := ih _ next
        refine ⟨old, ?_⟩
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact old symbol arity (by simpa [same] using found)
        · exact tail entry member
      · simp [checkArities, found, same] at success

/-- A consistent declared arity assignment cannot be rejected. -/
theorem check_complete [DecidableEq Symbol] (entries : List (Symbol × Nat))
    (before : Arities Symbol) (assignment : Symbol → Nat)
    (agrees : Extends assignment before) (describes : Describes assignment entries) :
    ∃ after, checkArities before entries = .ok after := by
  induction entries generalizing before with
  | nil => exact ⟨before, rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨symbol, arity⟩
    have head := describes (symbol, arity) (by simp)
    have tail : Describes assignment rest := fun entry member => describes entry (by simp [member])
    cases found : before symbol with
    | none =>
      have added : Extends assignment (insertArity before symbol arity) := by
        intro other value present
        by_cases same : other = symbol
        · subst other
          have equal : arity = value := by simpa [insertArity] using present
          simpa [equal] using head
        · exact agrees other value (by simpa [insertArity, same] using present)
      simpa [checkArities, found] using ih _ added tail
    | some expected =>
      have same : expected = arity := (agrees symbol expected found).symm.trans head
      simpa [checkArities, found, same] using ih before agrees tail

/-- Arity validation succeeds exactly when a consistent assignment exists. -/
theorem check_exact [DecidableEq Symbol] (entries : List (Symbol × Nat)) (before : Arities Symbol) :
    (∃ after, checkArities before entries = .ok after) ↔
      ∃ assignment, Extends assignment before ∧ Describes assignment entries := by
  constructor
  · rintro ⟨after, success⟩
    obtain ⟨old, entries⟩ := check_sound _ before after success
    refine ⟨fun symbol => (after symbol).getD 0, ?_, ?_⟩
    · intro symbol arity found; simp [old symbol arity found]
    · intro entry member; simp [entries entry member]
  · rintro ⟨assignment, agrees, describes⟩
    exact check_complete entries before assignment agrees describes

/-- Ordered graph rows, with transition constraints retained in each edge. -/
abbrev Rows (State Symbol : Type) := List (State × List (Edge State Symbol))

/-- Merge repeated keys in their original alternative order. -/
def rowFor [DecidableEq State] (rows : Rows State Symbol) (state : State) : List (Edge State Symbol) :=
  rows.flatMap fun (key, edges) => if key = state then edges else []

/-- Source map normalization retains one row for every original key. -/
def normalizeRows [DecidableEq State] [Ord State] (rows : Rows State Symbol) : Rows State Symbol :=
  ((distinct (rows.map Prod.fst)).mergeSort (fun a b => compare a b != .gt)).map
    fun state => (state, rowFor rows state)

/-- Merging rows does not lose or introduce any transition. -/
theorem rowFor_exact [DecidableEq State] (rows : Rows State Symbol) (state : State) (edge : Edge State Symbol) :
    edge ∈ rowFor rows state ↔ ∃ edges, (state, edges) ∈ rows ∧ edge ∈ edges := by
  simp only [rowFor, List.mem_flatMap]
  constructor
  · rintro ⟨⟨key, edges⟩, member, found⟩
    split at found
    · next same =>
        have equal : key = state := same
        subst key
        exact ⟨edges, member, found⟩
    · simp at found
  · rintro ⟨edges, member, found⟩
    exact ⟨(state, edges), member, by simpa using found⟩

/-- Row normalization preserves exactly the declared state names. -/
theorem normalized_keys [DecidableEq State] [Ord State] (rows : Rows State Symbol) (state : State) :
    state ∈ (normalizeRows rows).map Prod.fst ↔ state ∈ rows.map Prod.fst := by
  simp [normalizeRows, List.map_map, Function.comp_def, mem_distinct]

/-- Read all alternatives in table order. -/
def edges (rows : Rows State Symbol) : List (Edge State Symbol) := rows.flatMap Prod.snd

/-- Constructor declarations visited by the arity loop. -/
def arityEntries (rows : Rows State Symbol) : List (Symbol × Nat) :=
  (edges rows).map fun edge => (edge.label, edge.children.length)

/-- Initial-state, closed-graph, and ranked-alphabet failures. -/
inductive Error (State Symbol : Type) where
  | missingInitial : State → Error State Symbol
  | dangling : State → Error State Symbol
  | inconsistent : ArityError Symbol → Error State Symbol

/-- The first dangling child in the source table traversal order. -/
def dangling [DecidableEq State] (rows : Rows State Symbol) : Option State :=
  ((edges rows).flatMap Edge.children).find? fun child => !(child ∈ rows.map Prod.fst)

/-- Validate a normalized table in the source's error precedence. -/
def validateRows [DecidableEq State] [DecidableEq Symbol] (initial : State) (rows : Rows State Symbol) :
    Except (Error State Symbol) (Rows State Symbol) :=
  if initial ∈ rows.map Prod.fst then
    match dangling rows with
    | some child => .error (.dangling child)
    | none => match checkArities (fun _ => none) (arityEntries rows) with
      | .error error => .error (.inconsistent error)
      | .ok _ => .ok rows
  else .error (.missingInitial initial)

/-- The full public builder first merges duplicate rows. -/
def mkFTA [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (initial : State) (rows : Rows State Symbol) : Except (Error State Symbol) (Rows State Symbol) :=
  validateRows initial (normalizeRows rows)

/-- Closedness says that every child has a declared row. -/
def Closed (rows : Rows State Symbol) : Prop :=
  ∀ edge ∈ edges rows, ∀ child ∈ edge.children, child ∈ rows.map Prod.fst

/-- The dangling-state scan succeeds exactly for closed tables. -/
theorem dangling_none [DecidableEq State] (rows : Rows State Symbol) :
    dangling rows = none ↔ Closed rows := by
  simp [dangling, List.find?_eq_none, Closed]

/-- The mathematical conditions checked by the builder. -/
def Valid (initial : State) (rows : Rows State Symbol) : Prop :=
  initial ∈ rows.map Prod.fst ∧ Closed rows ∧ ∃ assignment, Describes assignment (arityEntries rows)

/-- A successful validation returns its whole table and exactly the required invariants. -/
theorem validateRows_exact [DecidableEq State] [DecidableEq Symbol]
    (initial : State) (rows : Rows State Symbol) :
    validateRows initial rows = .ok rows ↔ Valid initial rows := by
  by_cases initialPresent : initial ∈ rows.map Prod.fst
  · cases missing : dangling rows with
    | some child =>
      have notClosed : ¬Closed rows := by
        intro closed
        have none := (dangling_none rows).mpr closed
        simp [none] at missing
      simp [validateRows, initialPresent, missing, Valid, notClosed]
    | none =>
      have closed := (dangling_none rows).mp missing
      have arity : (∃ after, checkArities (fun _ => none) (arityEntries rows) = .ok after) ↔
          ∃ assignment, Describes assignment (arityEntries rows) := by
        simpa [Extends] using check_exact (arityEntries rows) (fun _ => none)
      cases result : checkArities (fun _ => none) (arityEntries rows) with
      | error failure =>
        have rejected : ¬∃ assignment, Describes assignment (arityEntries rows) := by
          intro witness
          obtain ⟨after, success⟩ := arity.mpr witness
          simp [result] at success
        simp [validateRows, initialPresent, missing, result, Valid, rejected]
      | ok after =>
        have described := arity.mp ⟨after, result⟩
        simp [validateRows, initialPresent, missing, result, Valid, closed, described]
  · simp [validateRows, initialPresent, Valid]

/-- Public construction succeeds exactly when its complete merged table is valid. -/
theorem mkFTA_exact [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (initial : State) (rows : Rows State Symbol) :
    mkFTA initial rows = .ok (normalizeRows rows) ↔ Valid initial (normalizeRows rows) :=
  validateRows_exact initial (normalizeRows rows)

/-- Merging repeated rows preserves the exact transition membership at each state. -/
theorem normalized_row_exact [DecidableEq State] [Ord State] (rows : Rows State Symbol)
    (state : State) (edge : Edge State Symbol) :
    edge ∈ rowFor (normalizeRows rows) state ↔ edge ∈ rowFor rows state := by
  rw [rowFor_exact]
  constructor
  · rintro ⟨outgoing, member, present⟩
    obtain ⟨key, _, same⟩ := List.mem_map.mp member
    have keyEqual : key = state := congrArg Prod.fst same
    have rowEqual : rowFor rows key = outgoing := congrArg Prod.snd same
    rw [← rowEqual, keyEqual] at present
    exact present
  · intro present
    have keyPresent : state ∈ rows.map Prod.fst := by
      obtain ⟨outgoing, member, _⟩ := (rowFor_exact rows state edge).mp present
      exact List.mem_map.mpr ⟨(state, outgoing), member, rfl⟩
    refine ⟨rowFor rows state, ?_, present⟩
    apply List.mem_map.mpr
    exact ⟨state, by simpa [mem_distinct] using keyPresent, rfl⟩

/-- Equal transition membership gives equal accepted languages, including cycles. -/
theorem accepts_transfer (before after : Automaton State Symbol)
    (rows : ∀ state edge, edge ∈ before state → edge ∈ after state)
    {state : State} {term : Term Symbol} (accepted : Accepts before state term) :
    Accepts after state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (Accepts after) states terms) with
  | node edge terms member runs guard ih => exact .node edge terms (rows _ _ member) ih guard
  | nil => exact .nil
  | cons head tail ihhead ihtail => exact .cons ihhead ihtail

/-- Duplicate-row normalization preserves all and only the original terms. -/
theorem normalized_language_exact [DecidableEq State] [Ord State]
    (rows : Rows State Symbol) (state : State) (term : Term Symbol) :
    Accepts (rowFor (normalizeRows rows)) state term ↔ Accepts (rowFor rows) state term :=
  ⟨accepts_transfer _ _ (fun state edge => (normalized_row_exact rows state edge).mp),
    accepts_transfer _ _ (fun state edge => (normalized_row_exact rows state edge).mpr)⟩

/-- Validation never returns a partially checked or truncated table. -/
theorem validateRows_returns [DecidableEq State] [DecidableEq Symbol]
    (initial : State) (rows result : Rows State Symbol)
    (success : validateRows initial rows = .ok result) : result = rows := by
  unfold validateRows at success
  split at success
  · split at success
    · simp at success
    · split at success
      · simp at success
      · exact (Except.ok.inj success).symm
  · simp at success

/-- A successful public builder returns the entire normalized table. -/
theorem mkFTA_returns [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (initial : State) (rows result : Rows State Symbol)
    (success : mkFTA initial rows = .ok result) : result = normalizeRows rows :=
  validateRows_returns initial (normalizeRows rows) result success

end MicroCFTA.FTAValidation
