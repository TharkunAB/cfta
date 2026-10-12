import Std

/-!
# Active construction occurrences and public query guards

The source stores these markers separately from size-index occurrence flags.
Every placeholder keeps its marker in every rebuild. Combinators combine
markers; completion removes only the definition that has finished. Public
queries reject remaining markers before reading temporary record fields.
-/
namespace MicroCFTA.RecursiveConstructionQueries

/-- Constructor provenance for the active tokens of a recursive record. -/
inductive Recipe where
  | source (tokens : List Nat)
  | occurrence (token : Nat)
  | preserve (inner : Recipe)
  | combine (inputs : List Recipe)
  | close (token : Nat) (inner : Recipe)

/-- Execute the source's empty, singleton, union, and deletion operations. -/
def active : Recipe → List Nat
  | .source tokens => tokens.eraseDups
  | .occurrence token => [token]
  | .preserve inner => active inner
  | .combine inputs => (inputs.flatMap active).eraseDups
  | .close token inner => (active inner).filter (· != token)
termination_by recipe => sizeOf recipe

/-- An independently stated free construction occurrence in the constructor tree. -/
def Open (token : Nat) : Recipe → Prop
  | .source tokens => token ∈ tokens
  | .occurrence current => token = current
  | .preserve inner => Open token inner
  | .combine inputs => ∃ input, ∃ (_present : input ∈ inputs), Open token input
  | .close current inner => token ≠ current ∧ Open token inner
termination_by recipe => sizeOf recipe

/-- The actual marker operations retain exactly the unclosed constructor occurrences. -/
theorem active_exact (token : Nat) (recipe : Recipe) : token ∈ active recipe ↔ Open token recipe := by
  cases recipe with
  | source tokens => simp [active, Open]
  | occurrence current => simp [active, Open]
  | preserve inner => simpa only [active, Open] using active_exact token inner
  | combine inputs =>
      simp only [active, List.mem_eraseDups, List.mem_flatMap, Open]
      constructor <;> rintro ⟨input, present, found⟩
      · exact ⟨input, present, (active_exact token input).mp found⟩
      · exact ⟨input, present, (active_exact token input).mpr found⟩
  | close current inner =>
      simp [active, Open, active_exact token inner, and_comm]
termination_by sizeOf recipe

/-- A completed record without external construction occurrences has no active marker. -/
theorem active_empty (recipe : Recipe) (closed : ∀ token, ¬Open token recipe) : active recipe = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro token present
  exact closed token ((active_exact token recipe).mp present)

/-- Completing an inner definition preserves each distinct enclosing marker. -/
theorem close_outer (outer inner : Nat) (different : outer ≠ inner) (recipe : Recipe)
    (present : outer ∈ active recipe) : outer ∈ active (.close inner recipe) := by
  simp [active, present, different]

/-- Closing a definition removes its token even when the source takes a finite shortcut. -/
theorem close_own (token : Nat) (recipe : Recipe) : token ∉ active (.close token recipe) := by
  simp [active]

/-- Complete payloads keep their construction markers independent of size metadata. -/
structure Record (Payload : Type) where
  payload : Payload
  construction : List Nat
  deriving DecidableEq

/-- Every rebuild supplies the same active marker beside its phase-specific payload. -/
def placeholder (token : Nat) (payload : Payload) : Record Payload := ⟨payload, [token]⟩

/-- Completed static sources and automaton imports have no active construction. -/
def closed (payload : Payload) : Record Payload := ⟨payload, []⟩

/-- Maps, labels, and pays preserve the marker field while changing their own payloads. -/
def preserve (payload : Result) (record : Record Payload) : Record Result := ⟨payload, record.construction⟩

/-- Products, choices, and heterogeneous joins combine the actual child marker sets. -/
def combine (payload : Result) (markers : List (List Nat)) : Record Result := ⟨payload, markers.flatten.eraseDups⟩

/-- Both cyclic completion and the unused-occurrence return path remove the completed token. -/
def finish (token : Nat) (record : Record Payload) : Record Payload :=
  { record with construction := record.construction.filter (· != token) }

/-- Group completion includes every probed body and removes only its own token. -/
def family (token : Nat) (payload : Result) (bodies : List (List Nat)) : Record Result :=
  finish token (combine payload bodies)

/-- Family queries remain blocked by any enclosing construction reached by a body. -/
theorem family_outer (outer inner : Nat) (payload : Result) (bodies : List (List Nat)) :
    outer ∈ (family inner payload bodies).construction ↔ outer ≠ inner ∧ ∃ body ∈ bodies, outer ∈ body := by
  simp [family, finish, combine, and_comm]

/-- Closing a record preserves every completed generation field exactly. -/
theorem finish_payload (token : Nat) (record : Record Payload) : (finish token record).payload = record.payload := rfl

/-- Construction rejection is separate from an original source error. -/
inductive Error (Cause : Type) where
  | source (cause : Cause)
  | queriedOccurrence
  deriving DecidableEq

/-- Source errors precede construction checks. Payload queries run only on closed records. -/
def query (read : Payload → Result) (input : Except Cause (Record Payload)) : Except (Error Cause) Result :=
  match input with
  | .error cause => .error (.source cause)
  | .ok record => if record.construction.isEmpty then .ok (read record.payload) else .error .queriedOccurrence

/-- A placeholder query has one stable error for every payload and every query operation. -/
theorem placeholder_query (token : Nat) (payload : Payload) (read : Payload → Result) :
    query (Cause := Cause) read (.ok (placeholder token payload)) = .error .queriedOccurrence := rfl

/-- Any retained active token blocks the temporary record before its payload is read. -/
theorem active_query (token : Nat) (record : Record Payload) (present : token ∈ record.construction)
    (read : Payload → Result) : query (Cause := Cause) read (.ok record) = .error .queriedOccurrence := by
  have nonempty : record.construction ≠ [] := by intro empty; simp [empty] at present
  simp [query, nonempty]

/-- Query results are independent of reconstruction phase while the occurrence is active. -/
theorem phase_independent (token : Nat) (first second : Payload) (read : Payload → Result) :
    query (Cause := Cause) read (.ok (placeholder token first)) = query read (.ok (placeholder token second)) := rfl

/-- Completed source queries retain their original payload behavior. -/
theorem closed_query (payload : Payload) (read : Payload → Result) :
    query (Cause := Cause) read (.ok (closed payload)) = .ok (read payload) := rfl

/-- Original construction errors retain precedence over query checks. -/
theorem source_error (read : Payload → Result) (cause : Cause) :
    query read (.error cause) = .error (.source cause) := rfl

/-- The public negative-rank check precedes record inspection. -/
def rankedQuery (negative : Int → Cause) (rank : Int) (read : Payload → Result)
    (input : Except Cause (Record Payload)) : Except (Error Cause) Result :=
  if rank < 0 then .error (.source (negative rank)) else query read input

/-- An active placeholder does not mask the existing negative-rank error. -/
theorem negative_first (negative : Int → Cause) (rank : Int) (below : rank < 0)
    (read : Payload → Result) (input : Except Cause (Record Payload)) :
    rankedQuery negative rank read input = .error (.source (negative rank)) := by simp [rankedQuery, below]

/-- The constructor metadata derives query readiness without a supplied closed-record flag. -/
theorem completed_query (payload : Payload) (recipe : Recipe) (complete : ∀ token, ¬Open token recipe)
    (read : Payload → Result) :
    query (Cause := Cause) read (.ok ⟨payload, active recipe⟩) = .ok (read payload) := by
  simp [query, active_empty recipe complete]

/-- The reproduced callback selects different branches when raw temporary support is exposed. -/
def chooseBody : Except (Error Unit) Bool → Nat
  | .ok true => 0
  | _ => 99

/-- The old raw observation differs between empty and live support rebuilds. -/
theorem old_builder_mismatch : chooseBody (.ok true) = 0 ∧ chooseBody (.ok false) = 99 := by decide

/-- The repaired callback observes one error and selects the same branch in both rebuilds. -/
theorem repaired_builder_agrees (token : Nat) :
    chooseBody (query id (.ok (placeholder token true))) = 99 ∧
      chooseBody (query id (.ok (placeholder token false))) = 99 := by constructor <;> rfl

/-- A finite return still closes the owning marker while keeping an enclosing marker. -/
theorem nested_completion (outer inner : Nat) (different : outer ≠ inner) (payload : Payload) :
    outer ∈ (finish inner (combine payload [[outer], [inner]])).construction ∧
      inner ∉ (finish inner (combine payload [[outer], [inner]])).construction ∧
      (finish outer (finish inner (combine payload [[outer], [inner]]))).construction = [] := by
  simp [finish, combine, different, Ne.symm different]

end MicroCFTA.RecursiveConstructionQueries
