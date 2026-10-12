import MicroCFTA.BinderSubstitution

/-!
# Closed binder exposure for bounded enumeration

The source unfolds Mu at the current depth. It substitutes the closed binder
for its own free reference before it exposes constructor rows. This module
checks that operation and its finite exposure worker. Fuel exhaustion remains
separate from the unreachable raw-reference error.
-/
namespace MicroCFTA.EnumerationBinderExposure
open Language Binding BinderLanguage

/-- Substitution introduces only references allowed by its actual replacements. -/
theorem substitute_free (shape : Shape Item) (substitution : Environment Item)
    (allowed : Nat → Prop)
    (resolved : ∀ name ∈ free shape, match substitution name with
      | none => allowed name
      | some replacement => ∀ reference ∈ free replacement, allowed reference) :
    ∀ reference ∈ free (substitute substitution shape), allowed reference := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ substitution : Environment Item, ∀ allowed : Nat → Prop,
      (∀ name ∈ freeList shapes, match substitution name with
        | none => allowed name
        | some replacement => ∀ reference ∈ free replacement, allowed reference) →
      ∀ reference ∈ freeList (substituteList substitution shapes), allowed reference)
    generalizing substitution allowed with
  | empty => simp [substitute, free]
  | ref name =>
      have result := resolved name (by simp [free])
      cases found : substitution name with
      | none => simpa [substitute, found, free] using result
      | some replacement => simpa [substitute, found] using result
  | branch payload children ih => exact ih substitution allowed resolved
  | alternatives edges ih => exact ih substitution allowed resolved
  | binder name body ih =>
      intro reference present
      have membership : reference ∈ free (substitute (mask substitution name) body) ∧ reference ≠ name := by
        simpa [substitute, free] using present
      have result := ih (mask substitution name) (fun other => other = name ∨ allowed other) (by
        intro other member
        by_cases same : other = name
        · simp [mask, same]
        · have original := resolved other (by simp [free, member, same])
          cases found : substitution other with
          | none => simpa [mask, same, found] using original
          | some replacement =>
              simp only [mask, same, ↓reduceIte, found]
              simp only [found] at original
              intro target targetMember
              exact Or.inr (original target targetMember)) reference membership.1
      exact result.resolve_left membership.2
  | nil =>
      rename_i substitution allowed resolved reference present
      simp [substituteList, freeList] at present
  | cons first rest ih ihtail =>
      rename_i substitution allowed resolved reference present
      simp only [substituteList, freeList, List.mem_append] at present
      rcases present with firstMember | restMember
      · exact ih substitution allowed (fun name member => resolved name (by simp [freeList, member])) reference firstMember
      · exact ihtail substitution allowed (fun name member => resolved name (by simp [freeList, member])) reference restMember

/-- Replacing every free reference by a closed shape produces a closed shape. -/
theorem substitute_closed (shape : Shape Item) (substitution : Environment Item)
    (resolved : ∀ name ∈ free shape, ∃ replacement, substitution name = some replacement ∧ free replacement = []) :
    free (substitute substitution shape) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reference present
  apply substitute_free shape substitution (fun _ => False) ?_ reference present
  intro name member
  obtain ⟨replacement, found, closed⟩ := resolved name member
  simp [found, closed]

/-- A free name in a closed binder body must be that binder's own name. -/
theorem closed_body_reference (name : Nat) (body : Shape Item)
    (closed : free (.binder name body) = []) (reference : Nat) (present : reference ∈ free body) :
    reference = name := by
  by_cases same : reference = name
  · exact same
  · have member : reference ∈ free (.binder name body) := by simp [free, present, same]
    simp [closed] at member

/-- Execute the same prepared self-substitution as outer binder unfolding. -/
def unfold (name : Nat) (body : Shape (Payload Symbol)) : Shape (Payload Symbol) :=
  prepare body (single name (.binder name body))

/-- Self-unfolding of a closed binder cannot expose an unbound reference. -/
theorem unfold_closed (name : Nat) (body : Shape (Payload Symbol))
    (closed : free (.binder name body) = []) : free (unfold name body) = [] := by
  rw [unfold, prepare_correct]
  apply substitute_closed
  intro reference present
  have same := closed_body_reference name body closed reference present
  exact ⟨.binder name body, by simp [single, same], closed⟩

/-- Closedness discharges all freshness premises of the source unfolding law. -/
theorem unfold_exact (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol))
    (closed : free (.binder name body) = []) :
    meaning environment (unfold name body) = meaning environment (.binder name body) := by
  rw [unfold, prepare_correct]
  apply unfold_substitution
  intro binderName member reference replacement found
  have same : replacement = .binder name body := by
    by_cases hit : reference = name
    · simpa [single, hit] using found.symm
    · simp [single, hit] at found
  simp [same, closed]

/-- Unfolding consumes no constructor depth. -/
theorem unfold_bounded_exact (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol))
    (closed : free (.binder name body) = []) (height : Nat) (term : Term Symbol) :
    (meaning environment (unfold name body) term ∧ term.height ≤ height) ↔
      meaning environment (.binder name body) term ∧ term.height ≤ height := by
  rw [unfold_exact environment name body closed]

/-- A selected child of a closed constructor or union is closed. -/
theorem closed_member (shapes : List (Shape (Payload Symbol))) (closed : freeList shapes = [])
    (shape : Shape (Payload Symbol)) (member : shape ∈ shapes) : free shape = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reference present
  have found := freeList_member shapes shape member reference present
  simp [closed] at found

/-- The source can unfold, select a union member, or descend to a constructor child. -/
inductive RequestStep : Shape (Payload Symbol) → Shape (Payload Symbol) → Prop where
  | unfold (name body) : RequestStep (.binder name body) (unfold name body)
  | alternative (shapes) (shape) : shape ∈ shapes → RequestStep (.alternatives shapes) shape
  | child (payload) (children) (child) : child ∈ children → RequestStep (.branch payload children) child

/-- Every actual recursive request preserves closedness. -/
theorem request_closed {before after : Shape (Payload Symbol)}
    (step : RequestStep before after) (closed : free before = []) : free after = [] := by
  cases step with
  | unfold name body => exact unfold_closed name body closed
  | alternative shapes selected member => exact closed_member shapes closed _ member
  | child payload children selected member => exact closed_member children closed _ member

/-- A finite source traversal consists of these actual primitive requests. -/
inductive Reachable (root : Shape (Payload Symbol)) : Shape (Payload Symbol) → Prop where
  | root : Reachable root root
  | step {before after} : Reachable root before → RequestStep before after → Reachable root after

/-- Every requested shape remains closed, regardless of traversal order or sharing. -/
theorem reachable_closed {root shape : Shape (Payload Symbol)} (closed : free root = [])
    (reachable : Reachable root shape) : free shape = [] := by
  induction reachable with
  | root => exact closed
  | step previous step ih => exact request_closed step ih

/-- The unexpected-Rec branch is unreachable from any closed input. -/
theorem no_unexpected_reference {root : Shape (Payload Symbol)} (closed : free root = []) (name : Nat) :
    ¬ Reachable root (.ref name) := by
  intro reachable
  have impossible := reachable_closed closed reachable
  simp [free] at impossible

/-- A constructor row retains its full payload and ordered child shapes. -/
abbrev Row (Symbol : Type) := Payload Symbol × List (Shape (Payload Symbol))

/-- An execution limit does not mean that the represented language is empty. -/
inductive Error where
  | fuelExhausted
  | unresolvedReference (name : Nat)
  deriving DecidableEq, Repr

/-- Collect the ordered rows of every union member. -/
def collect (visit : Shape (Payload Symbol) → Except Error (List (Row Symbol))) :
    List (Shape (Payload Symbol)) → Except Error (List (Row Symbol))
  | [] => .ok []
  | first :: rest =>
      match visit first with
      | .error error => .error error
      | .ok rows => match collect visit rest with
        | .error error => .error error
        | .ok remaining => .ok (rows ++ remaining)

/-- Expose a constructor layer without consuming any constructor height. -/
def expose : Nat → Shape (Payload Symbol) → Except Error (List (Row Symbol))
  | 0, _ => .error .fuelExhausted
  | _ + 1, .empty => .ok []
  | _ + 1, .ref name => .error (.unresolvedReference name)
  | _ + 1, .branch payload children => .ok [(payload, children)]
  | fuel + 1, .alternatives members => collect (expose fuel) members
  | fuel + 1, .binder name body => expose fuel (unfold name body)

/-- Read exposed rows without changing any payload or child language. -/
def rowsMeaning (environment : Env Symbol) (rows : List (Row Symbol)) (term : Term Symbol) : Prop :=
  ∃ row ∈ rows, meaning environment (.branch row.1 row.2) term

/-- All constructor children returned by exposure are closed. -/
def RowsClosed (rows : List (Row Symbol)) : Prop :=
  ∀ row ∈ rows, ∀ child ∈ row.2, free child = []

/-- Successful collection visits every input and returns exactly their rows. -/
theorem collect_success (visit : Shape (Payload Symbol) → Except Error (List (Row Symbol)))
    (shapes : List (Shape (Payload Symbol))) (rows : List (Row Symbol))
    (success : collect visit shapes = .ok rows) :
    (∀ shape ∈ shapes, ∃ result, visit shape = .ok result) ∧
    (∀ row, row ∈ rows ↔ ∃ shape ∈ shapes, ∃ result, visit shape = .ok result ∧ row ∈ result) := by
  induction shapes generalizing rows with
  | nil =>
      simp [collect] at success
      subst rows
      simp
  | cons first rest ih =>
      cases head : visit first with
      | error error => simp [collect, head] at success
      | ok headRows =>
          cases tail : collect visit rest with
          | error error => simp [collect, head, tail] at success
          | ok tailRows =>
              have same : headRows ++ tailRows = rows := by simpa [collect, head, tail] using success
              subst rows
              obtain ⟨all, members⟩ := ih tailRows tail
              constructor
              · intro shape member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨headRows, head⟩
                · exact all shape member
              · intro row
                constructor
                · intro member
                  rcases List.mem_append.mp member with member | member
                  · exact ⟨first, by simp, headRows, head, member⟩
                  · obtain ⟨shape, member, result, found, rowMember⟩ := (members row).mp member
                    exact ⟨shape, by simp [member], result, found, rowMember⟩
                · rintro ⟨shape, member, result, found, rowMember⟩
                  rcases List.mem_cons.mp member with rfl | member
                  · have same : result = headRows := by simpa [head] using found.symm
                    subst result
                    exact List.mem_append_left _ rowMember
                  · exact List.mem_append_right _ ((members row).mpr ⟨shape, member, result, found, rowMember⟩)

/-- Collection cannot invent an unresolved-reference error. -/
theorem collect_no_reference (visit : Shape (Payload Symbol) → Except Error (List (Row Symbol)))
    (shapes : List (Shape (Payload Symbol)))
    (safe : ∀ shape ∈ shapes, ∀ name, visit shape ≠ .error (.unresolvedReference name)) (name : Nat) :
    collect visit shapes ≠ .error (.unresolvedReference name) := by
  induction shapes with
  | nil => simp [collect]
  | cons first rest ih =>
      cases head : visit first with
      | error error =>
          simpa [collect, head] using safe first (by simp) name
      | ok rows =>
          cases tail : collect visit rest with
          | error error => simpa [collect, head, tail] using ih (fun shape member => safe shape (by simp [member]))
          | ok remaining => simp [collect, head, tail]

/-- The executable exposure worker preserves exact rows and cannot return raw Rec. -/
theorem expose_spec (fuel : Nat) (shape : Shape (Payload Symbol)) (closed : free shape = []) :
    (∀ name, expose fuel shape ≠ .error (.unresolvedReference name)) ∧
    (∀ rows, expose fuel shape = .ok rows → RowsClosed rows ∧
      ∀ environment term, rowsMeaning environment rows term ↔ meaning environment shape term) := by
  induction fuel generalizing shape with
  | zero => simp [expose]
  | succ fuel ih =>
      cases shape with
      | empty => simp [expose, RowsClosed, rowsMeaning, meaning]
      | ref name => simp [free] at closed
      | branch payload children =>
          constructor
          · simp [expose]
          · intro rows success
            have same : rows = [(payload, children)] := by simpa [expose] using success.symm
            subst rows
            constructor
            · intro row member child childMember
              have same : row = (payload, children) := by simpa using member
              subst row
              exact closed_member children closed child childMember
            · intro environment term
              simp [rowsMeaning]
      | binder name body =>
          obtain ⟨safe, exact⟩ := ih (unfold name body) (unfold_closed name body closed)
          constructor
          · exact safe
          · intro rows success
            obtain ⟨children, languages⟩ := exact rows success
            exact ⟨children, fun environment term => by
              rw [languages, unfold_exact environment name body closed]⟩
      | alternatives shapes =>
          have each := fun child member => ih child (closed_member shapes closed child member)
          constructor
          · exact collect_no_reference (expose fuel) shapes (fun child member => (each child member).1)
          · intro rows success
            obtain ⟨visited, members⟩ := collect_success (expose fuel) shapes rows success
            constructor
            · intro row member child childMember
              obtain ⟨shape, member, result, found, rowMember⟩ := (members row).mp member
              exact ((each shape member).2 result found).1 row rowMember child childMember
            · intro environment term
              simp only [meaning]
              constructor
              · rintro ⟨row, member, accepted⟩
                obtain ⟨shape, member, result, found, rowMember⟩ := (members row).mp member
                exact ⟨⟨shape, member⟩, (((each shape member).2 result found).2 environment term).mp
                  ⟨row, rowMember, accepted⟩⟩
              · rintro ⟨⟨shape, member⟩, accepted⟩
                obtain ⟨result, found⟩ := visited shape member
                obtain ⟨row, rowMember, accepted⟩ := (((each shape member).2 result found).2 environment term).mpr accepted
                exact ⟨row, (members row).mpr ⟨shape, member, result, found, rowMember⟩, accepted⟩

/-- The finite exposure worker preserves the bound used by the concrete row builder. -/
theorem expose_bounded_exact (fuel : Nat) (shape : Shape (Payload Symbol))
    (closed : free shape = []) (rows : List (Row Symbol)) (success : expose fuel shape = .ok rows)
    (environment : Env Symbol) (height : Nat) (term : Term Symbol) :
    (rowsMeaning environment rows term ∧ term.height ≤ height) ↔
      meaning environment shape term ∧ term.height ≤ height := by
  rw [((expose_spec fuel shape closed).2 rows success).2 environment term]

/-- A closed input can report only an execution limit, never an unresolved reference. -/
theorem expose_error_fuel (fuel : Nat) (shape : Shape (Payload Symbol))
    (closed : free shape = []) (error : Error) (failed : expose fuel shape = .error error) :
    error = .fuelExhausted := by
  cases error with
  | fuelExhausted => rfl
  | unresolvedReference name => exact False.elim ((expose_spec fuel shape closed).1 name failed)

/-- Every child request made from successfully exposed rows is closed. -/
theorem exposed_child_closed (fuel : Nat) (shape : Shape (Payload Symbol))
    (closed : free shape = []) (rows : List (Row Symbol)) (success : expose fuel shape = .ok rows)
    (row : Row Symbol) (member : row ∈ rows) (child : Shape (Payload Symbol)) (present : child ∈ row.2) :
    free child = [] :=
  ((expose_spec fuel shape closed).2 rows success).1 row member child present

end MicroCFTA.EnumerationBinderExposure
