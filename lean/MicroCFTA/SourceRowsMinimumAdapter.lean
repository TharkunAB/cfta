import MicroCFTA.SourceRowsMinimumShape
import MicroCFTA.SourceInternedRows

/-!
# Polymorphic minimum sizes over the shared interned adapter

The minimum table reads the actual toRows keys and transition children.
Constraints remain arbitrary data at this stage. This calculation proves
structural productivity, not the satisfiability of stored constraints.
EmptyState remains separate from every interned identity.
-/

namespace MicroCFTA.SourceRowsMinimumAdapter

open Language SourceInternedRows

/-- A transition's structural language keeps its symbol and children and erases its payload. -/
def ordinary (edge : Transition Symbol Constraint) : Language.Edge State Symbol :=
  ⟨edge.label, edge.children, fun _ => true⟩

/-- Read actual raw adapter rows with structural guards. -/
def automaton (table : List (State × List (Transition Symbol Constraint))) : Language.Automaton State Symbol :=
  fun state => (lookup table state).map ordinary

/-- Every structural row is plain regardless of its constraint payload. -/
theorem plain (table : List (State × List (Transition Symbol Constraint))) : Decoder.Plain (automaton table) := by
  intro state edge member term
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rfl

/-- Only actual map keys can have nonempty rows; the infinite State type is not a finite-domain premise. -/
theorem supported (table : List (State × List (Transition Symbol Constraint))) :
    SourceRowsMinimum.Supported (automaton table) (table.map Prod.fst) := by
  intro state edge present
  obtain ⟨transition, listed, same⟩ := List.mem_map.mp present
  obtain ⟨⟨key, outgoing⟩, row, found⟩ := List.mem_flatMap.mp listed
  by_cases equal : key = state
  · exact List.mem_map.mpr ⟨(key, outgoing), row, equal⟩
  · simp [equal] at found

/-- The source minimum calculation over the actual polymorphic transition map. -/
def minimumSizes (table : List (State × List (Transition Symbol Constraint))) : State → Option Nat :=
  SourceRowsMinimum.minimumSizes (automaton table) (table.map Prod.fst)

/-- The polymorphic source minimum table finishes with a stable ordinary sweep. -/
theorem finite (table : List (State × List (Transition Symbol Constraint))) :
    ∃ fuel, MinimumSize.sweeps (automaton table) (table.map Prod.fst) fuel (fun _ => none) = minimumSizes table ∧
      MinimumSize.sweep (automaton table) (table.map Prod.fst) (minimumSizes table) = minimumSizes table :=
  SourceRowsMinimum.terminates (automaton table) (table.map Prod.fst)

/-- Every stored number is precisely the least structural accepted node count. -/
theorem minimum_exact (table : List (State × List (Transition Symbol Constraint))) (state : State) (size : Nat) :
    minimumSizes table state = some size ↔
      (∃ term, Accepts (automaton table) state term ∧ RecursiveSize.nodeSize term = size) ∧
      (∀ term, Accepts (automaton table) state term → size ≤ RecursiveSize.nodeSize term) :=
  SourceRowsMinimum.correct (automaton table) (plain table) _ (supported table) state size

/-- An absent entry has no finite structural witness. -/
theorem minimum_none (table : List (State × List (Transition Symbol Constraint))) (state : State) :
    minimumSizes table state = none ↔ ∀ term, ¬Accepts (automaton table) state term :=
  SourceRowsMinimum.none_iff (automaton table) (plain table) _ (supported table) state

/-- Replace constraint payloads without changing any row key, label, or ordered child list. -/
def mapConstraints (f : First → Second) (table : List (State × List (Transition Symbol First))) :
    List (State × List (Transition Symbol Second)) :=
  table.map fun (state, edges) => (state, edges.map fun edge => ⟨edge.label, edge.children, f edge.constraint⟩)

/-- The actual ordinary readback is unchanged by arbitrary constraint mapping. -/
theorem constraints_automaton (f : First → Second) (table : List (State × List (Transition Symbol First))) :
    automaton (mapConstraints f table) = automaton table := by
  funext state
  simp only [automaton, lookup, mapConstraints, List.flatMap_map, List.map_flatMap]
  congr 1
  funext entry
  rcases entry with ⟨key, outgoing⟩
  by_cases same : key = state <;> simp [same, List.map_map, Function.comp_def, ordinary]

/-- Erasing constraints to unit, or replacing them with any payload, leaves the computed table identical. -/
theorem constraint_independent (f : First → Second) (table : List (State × List (Transition Symbol First))) :
    minimumSizes (mapConstraints f table) = minimumSizes table := by
  unfold minimumSizes
  rw [constraints_automaton]
  simp [mapConstraints, List.map_map, Function.comp_def]

/-- Relabel each transition while preserving its children and payload. -/
def mapLabels (f : First → Second) (table : List (State × List (Transition First Constraint))) :
    List (State × List (Transition Second Constraint)) :=
  table.map fun (state, edges) => (state, edges.map fun edge => ⟨f edge.label, edge.children, edge.constraint⟩)

/-- Even a noninjective symbol relabeling cannot change a structural minimum size. -/
theorem label_independent (f : First → Second) (table : List (State × List (Transition First Constraint))) :
    minimumSizes (mapLabels f table) = minimumSizes table := by
  unfold minimumSizes
  have keys : (mapLabels f table).map Prod.fst = table.map Prod.fst := by simp [mapLabels, List.map_map, Function.comp_def]
  rw [keys]
  apply SourceRowsMinimumShape.minimum_shape
  intro state
  simp only [automaton, lookup, mapLabels, List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  funext entry
  rcases entry with ⟨key, outgoing⟩
  by_cases same : key = state <;> simp [same, List.map_map, Function.comp_def, ordinary]

/-- An explicitly empty row and an absent row have the same absent minimum. -/
theorem empty_row (table : List (State × List (Transition Symbol Constraint))) (state : State)
    (empty : lookup table state = []) : minimumSizes table state = none := by
  apply (minimum_none table state).mpr
  intro term accepted
  cases accepted with
  | node edge children member accepted guarded => simp [automaton, empty] at member

/-- No nonempty traversal can assign a finite size to the EmptyState sentinel. -/
theorem empty_state (heap : Heap Symbol Constraint) (visited : List Nat) :
    minimumSizes (table heap visited) .empty = none :=
  empty_row _ _ (table_empty heap visited)

/-- The separate empty constructor cannot alias any interned identity. -/
theorem empty_separate (identity : Nat) : State.empty ≠ .interned identity := by intro impossible; cases impossible

/-- The empty-root adapter map has no productive state. -/
theorem empty_root (state : State) : minimumSizes ([⟨State.empty, []⟩] : List (State × List (Transition Symbol Constraint))) state = none := by
  apply empty_row
  simp [lookup]

/-- The source productiveRows precheck and finite-table lookup. -/
def productiveRows (table : List (State × List (Transition Symbol Constraint))) (state : State) : Bool :=
  !(lookup table state).isEmpty && (minimumSizes table state).isSome

/-- Actual minimum-size convergence derives the exact structural productivity test. -/
theorem productive_exact (table : List (State × List (Transition Symbol Constraint))) (state : State) :
    productiveRows table state = true ↔ ∃ term, Accepts (automaton table) state term := by
  constructor
  · intro yes
    have parts : (lookup table state).isEmpty = false ∧ (minimumSizes table state).isSome = true := by
      simpa [productiveRows] using yes
    have found := parts.2
    obtain ⟨size, present⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨term, accepted, _⟩ := ((minimum_exact table state size).mp present).1
    exact ⟨term, accepted⟩
  · rintro ⟨term, accepted⟩
    have nonempty : (lookup table state).isEmpty = false := by
      cases accepted with
      | node edge children member accepted guarded =>
          obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
          exact List.isEmpty_eq_false_iff.mpr (fun empty => by simp only [empty, List.not_mem_nil] at present)
    cases found : minimumSizes table state with
    | none => exact False.elim (((minimum_none table state).mp found) term accepted)
    | some size => simp [productiveRows, nonempty, found]

end MicroCFTA.SourceRowsMinimumAdapter
