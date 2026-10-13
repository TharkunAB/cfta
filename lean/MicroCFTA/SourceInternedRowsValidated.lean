import MicroCFTA.SourceInternedRowsLanguage

/-!
# Validation after interned row exposure

`toFTA` rejects an open root before the traversal. Completed row exposure
then calls the existing ordered FTA validator. The source omits EmptyState
from every nonempty-root table. Closedness therefore uses the constructor
invariant that no retained edge has an empty child.
-/
namespace MicroCFTA.SourceInternedRows
open Language FTAValidation

/-- The two public conversion failures remain distinct. -/
inductive ViewError (Symbol : Type) where
  | openNode
  | invalidFTA (error : FTAValidation.Error State Symbol)

/-- Source conversion checks free variables before reading and validating rows. -/
def toFTA [DecidableEq Symbol] (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (hasFree : Bool) (fuel : Nat) (root : Ref) : Option (Except (ViewError Symbol) (Rows State Symbol)) :=
  if hasFree then some (.error .openNode)
  else (toRows heap fuel root).map fun table =>
    (mkFTA (stateOf root) (interpretedRows holds table)).mapError ViewError.invalidFTA

/-- Open-root rejection requires neither row exposure nor validation. -/
theorem open_rejected [DecidableEq Symbol] (heap : Heap Symbol Constraint)
    (holds : Constraint → Term Symbol → Bool) (fuel : Nat) (root : Ref) :
    toFTA heap holds true fuel root = some (.error .openNode) := rfl

/-- A successful public result contains the whole normalized exposed table. -/
theorem toFTA_rows [DecidableEq Symbol] (heap : Heap Symbol Constraint)
    (holds : Constraint → Term Symbol → Bool) (hasFree : Bool) (fuel : Nat) (root : Ref)
    (result : Rows State Symbol) (done : toFTA heap holds hasFree fuel root = some (.ok result)) :
    hasFree = false ∧ ∃ raw, toRows heap fuel root = some raw ∧
      mkFTA (stateOf root) (interpretedRows holds raw) = .ok result ∧
      ∀ state, rowFor result state = rowFor (interpretedRows holds raw) state := by
  cases hasFree with
  | true => simp [toFTA] at done
  | false =>
    obtain ⟨raw, read, checked⟩ := Option.map_eq_some_iff.mp done
    cases validated : mkFTA (stateOf root) (interpretedRows holds raw) with
    | error error => simp [validated, Except.mapError] at checked
    | ok table =>
      have same : table = result := by simpa [validated, Except.mapError] using checked
      subst table
      refine ⟨rfl, raw, read, validated, ?_⟩
      intro state
      rw [mkFTA_returns _ _ result validated]
      exact SourceFromTerms.normalize_lookup _ _

/-- Successful `toFTA` validation preserves the complete guarded root language. -/
theorem toFTA_language [DecidableEq Symbol] (heap : Heap Symbol Constraint)
    (holds : Constraint → Term Symbol → Bool) (hasFree : Bool) (fuel : Nat) (root : Ref)
    (result : Rows State Symbol) (done : toFTA heap holds hasFree fuel root = some (.ok result))
    (term : Term Symbol) : Accepts (rowFor result) (stateOf root) term ↔ Accepts (graph heap holds) (stateOf root) term := by
  obtain ⟨_, raw, read, _, exactRows⟩ := toFTA_rows heap holds hasFree fuel root result done
  have same := funext exactRows
  rw [same]
  exact toRows_language heap holds fuel root raw read term

/-- Native smart constructors exclude empty child references in retained reachable rows. -/
def NoEmptyBelow (heap : Heap Symbol Constraint) (root : Ref) : Prop :=
  ∀ identity, Reaches heap [root] identity → ∀ row ∈ heap identity, none ∉ row.children

/-- The exact declared keys of a nonempty source table. -/
theorem table_keys (heap : Heap Symbol Constraint) (visited : List Nat) (state : State) :
    state ∈ (table heap visited).map Prod.fst ↔ ∃ identity ∈ visited, state = .interned identity := by
  simp [table, List.map_map, Function.comp_def, CanonicalClasses.mem_sortedSet, eq_comm]

/-- Constraint interpretation does not change any state declaration. -/
theorem interpreted_keys (holds : Constraint → Term Symbol → Bool)
    (raw : List (State × List (Transition Symbol Constraint))) :
    (interpretedRows holds raw).map Prod.fst = raw.map Prod.fst := by
  simp [interpretedRows, List.map_map, Function.comp_def]

/-- Every nonempty child is declared by the actual traversal; empty children are excluded by the retained-row invariant. -/
theorem toRows_closed (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (fuel : Nat) (root : Ref) (result : List (State × List (Transition Symbol Constraint)))
    (done : toRows heap fuel root = some result) (noEmpty : NoEmptyBelow heap root) :
    Closed (interpretedRows holds result) := by
  cases root with
  | none =>
    cases Option.some.inj done
    simp [Closed, edges, interpretedRows]
  | some root =>
    obtain ⟨visited, walked, same⟩ := Option.map_eq_some_iff.mp done
    subst result
    intro edge member child childIn
    obtain ⟨⟨state, outgoing⟩, row, edgeIn⟩ := List.mem_flatMap.mp member
    have found := (rowFor_exact _ _ _).mpr ⟨outgoing, row, edgeIn⟩
    cases state with
    | empty => simp [interpreted_empty] at found
    | interned identity =>
      rw [interpreted_table] at found
      split at found
      · rename_i present
        obtain ⟨raw, rawIn, sameEdge⟩ := List.mem_map.mp found
        subst edge
        obtain ⟨ref, refIn, rfl⟩ := List.mem_map.mp childIn
        have reached := (collect_exact heap fuel [some root] visited walked identity).mp present
        cases ref with
        | none => exact False.elim (noEmpty identity reached raw rawIn refIn)
        | some next =>
          have nextReached : Reaches heap [some root] next := .child reached
            ((mem_successors heap identity next).mpr (List.mem_flatMap.mpr ⟨raw, rawIn, refIn⟩))
          rw [interpreted_keys]
          exact (table_keys heap visited _).mpr ⟨next,
            (collect_exact heap fuel [some root] visited walked next).mpr nextReached, rfl⟩
      · simp at found

/-- Finite exposure gives a finite public result, including a possible arity error. -/
theorem toFTA_finite [DecidableEq Symbol] (heap : Heap Symbol Constraint)
    (holds : Constraint → Term Symbol → Bool) (domain : List Nat) (closed : ClosedDomain heap domain)
    (hasFree : Bool) (root : Ref) (supported : ∀ identity, root = some identity → identity ∈ domain) :
    ∃ fuel result, ∀ larger, fuel ≤ larger → toFTA heap holds hasFree larger root = some result := by
  cases hasFree with
  | true => exact ⟨0, .error .openNode, fun _ _ => rfl⟩
  | false =>
    obtain ⟨fuel, raw, done⟩ := toRows_finite heap domain closed root supported
    exact ⟨fuel, (mkFTA (stateOf root) (interpretedRows holds raw)).mapError ViewError.invalidFTA,
      fun larger enough => by simp [toFTA, done larger enough]⟩

/-- Omitting the constructor invariant produces the source's real dangling EmptyState case. -/
theorem empty_child_missing (heap : Heap Symbol Constraint) (visited : List Nat) :
    State.empty ∉ (table heap visited).map Prod.fst := by simp [table_keys]

end MicroCFTA.SourceInternedRows
