import MicroCFTA.EqualityRawLeafUnion
import MicroCFTA.EqualityOrdinaryUnionSource

/-!
# Actual ordinary source path projection

Each proper path reads its selected child from every stored source edge.
Missing positions issue no child request. The source then makes one union
from all returned projections. Recursive roots remain outside this worker;
the ordinary occurrence invariant excludes those branches.
-/
namespace MicroCFTA.EqualityLeafProjectionPathWorker
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRequireAvailability
open EqualityLeafProjectionWorkers (bindOptional bindOptional_safe bindOptional_returns Returns pure_returns)
open EqualityLeafProjectionSyntax (Path)
open EqualityOrdinaryUnionSource (sourceUnion)

/-- Copy the source mapMaybe traversal in actual canonical edge order. -/
def rows (project : Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard))) (index : Nat) :
    List (EdgeValue Symbol Guard) → Work Symbol Guard (Option (List (Value Symbol Guard)))
  | [] => .pure (some [])
  | edge :: rest => match edge.children[index]? with
    | none => rows project index rest
    | some child => bindOptional (project child) fun value =>
        bindOptional (rows project index rest) fun values => .pure (some (value :: values))

/-- Execute ordinary source getPath with one physical union per proper path step. -/
def read : Path → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard))
  | [], value => .pure (some value)
  | index :: path, value => match value with
    | .empty => .pure (some .empty)
    | .node _ edges _ _ => bindOptional (rows (read path) index edges) fun values =>
        (sourceUnion values).bind fun result => .pure (some result)
    | .reference .. | .union .. | .mu .. => .pure none

/-- Source forest root projection is union; an absent child position is EmptyNode. -/
def readForest (path : Path) (values : List (Value Symbol Guard)) : Work Symbol Guard (Option (Value Symbol Guard)) :=
  match path with
  | [] => (sourceUnion values).bind fun value => .pure (some value)
  | index :: rest => match values[index]? with
    | none => .pure (some .empty)
    | some value => read rest value

/-- Optional source projection has no effect for missing positions. -/
theorem rows_safe (project : Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (safe : ∀ value, Safe (project value)) (index : Nat) (edges : List (EdgeValue Symbol Guard)) : Safe (rows project index edges) := by
  induction edges with
  | nil => trivial
  | cons edge rest ih =>
      unfold rows
      split
      · exact ih
      · exact bindOptional_safe _ _ (safe _) (fun _ => bindOptional_safe _ _ ih (fun _ => trivial))

/-- All finite ordinary projection requests preserve complete source key fields. -/
theorem read_safe (path : Path) (value : Value Symbol Guard) : Safe (read path value) := by
  induction path generalizing value with
  | nil => trivial
  | cons index path ih =>
      cases value <;> first
        | trivial
        | exact bindOptional_safe _ _ (rows_safe (read path) ih index _) (fun values =>
            safe_bind _ _ (makeNode_safe (values.flatMap nodeEdges)) (fun _ => trivial))

/-- Every ordinary child membership follows from the finite worker invariant. -/
theorem ordinary_child (edges : List (EdgeValue Symbol Guard))
    (ordinary : EqualityLeafProjectionWorkers.OrdinaryEdges edges)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges)
    (child : Value Symbol Guard) (present : child ∈ edge.children) : EqualityLeafProjectionWorkers.Ordinary child := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          rcases List.mem_cons.mp member with same | tail
          · subst edge
            have all := ordinary.1
            change child ∈ children at present
            clear ordinary ih member
            induction children with
            | nil => cases present
            | cons head tail tailIH =>
                rcases List.mem_cons.mp present with same | member
                · exact same ▸ all.1
                · exact tailIH all.2 member
          · exact ih ordinary.2 tail

/-- Selected ordinary projections complete in every actual intermediate cache. -/
theorem rows_returns [DecidableEq (EdgeKey Symbol Guard)]
    (project : Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (index : Nat) (edges : List (EdgeValue Symbol Guard))
    (complete : ∀ edge ∈ edges, ∀ child ∈ edge.children, ∀ state, Returns (project child) state)
    (state : State Symbol Guard) : Returns (rows project index edges) state := by
  induction edges generalizing state with
  | nil => exact pure_returns [] state
  | cons edge rest ih =>
      simp only [rows]
      split
      · exact ih (fun value member => complete value (by simp [member])) state
      · rename_i child selected
        exact bindOptional_returns _ _ state (complete edge (by simp) child (List.mem_of_getElem? selected) state)
          (fun _ current => bindOptional_returns _ _ current
            (ih (fun value member => complete value (by simp [member])) current)
            (fun _ later => pure_returns _ later))

/-- Ordinary source path projection cannot reach the unsupported-constructor result. -/
theorem read_returns [DecidableEq (EdgeKey Symbol Guard)] (path : Path) (value : Value Symbol Guard)
    (ordinary : EqualityLeafProjectionWorkers.Ordinary value) (state : State Symbol Guard) : Returns (read path value) state := by
  induction path generalizing value state with
  | nil => exact pure_returns value state
  | cons index path ih =>
      cases value with
      | empty => exact pure_returns (Value.empty : Value Symbol Guard) state
      | node entry edges depth free =>
          apply bindOptional_returns _ _ state (rows_returns (read path) index edges
            (fun edge member child present current => ih child (ordinary_child edges ordinary edge member child present) current) state)
          intro values current
          refine ⟨(run (sourceUnion values) current).1, ?_⟩
          simp only [run_bind, run]
      | reference | union | mu => cases ordinary

/-- Actual physical union preserves complete projection output payloads. -/
theorem union_checked [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (available : ChildrenAvailable state values) :
    Checked Available ((sourceUnion values).bind fun value => .pure (some value)) state := by
  have result := EqualityOrdinaryUnionSource.sourceUnion_available values state facts available
  simp only [Checked, run_bind, run]
  refine ⟨result.1, ?_⟩
  intro value same
  cases Option.some.inj same
  exact result.2

/-- Ordered source projections retain every available child through later siblings. -/
theorem rows_available [DecidableEq (EdgeKey Symbol Guard)]
    (project : Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (checked : ∀ value state, Facts state → Available state value → Checked Available (project value) state)
    (index : Nat) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : ∀ edge ∈ edges, ChildrenAvailable state edge.children) :
    Checked ChildrenAvailable (rows project index edges) state := by
  induction edges generalizing state with
  | nil => exact ⟨facts, by intro values same; cases Option.some.inj same; simp [ChildrenAvailable]⟩
  | cons edge rest ih =>
      simp only [rows]
      split
      · exact ih state facts (fun value member => available value (by simp [member]))
      · rename_i child selected
        have childFacts := checked child state facts (available edge (by simp) child (List.mem_of_getElem? selected))
        apply bindOptional_checked _ _ state Available ChildrenAvailable childFacts
        intro value valueAvailable
        let middle := (run (project child) state).2
        have restAvailable : ∀ edge ∈ rest, ChildrenAvailable middle edge.children := by
          intro edge member child present
          exact available_after_run (project _) state facts.coherent.valid (available edge (by simp [member]) child present)
        have restFacts := ih middle childFacts.1 restAvailable
        apply bindOptional_checked _ _ middle ChildrenAvailable ChildrenAvailable restFacts
        intro values valuesAvailable
        have retained := available_after_run (rows project index rest) middle childFacts.1.coherent.valid valueAvailable
        refine ⟨restFacts.1, ?_⟩
        intro result same
        cases Option.some.inj same
        intro selected member
        rcases List.mem_cons.mp member with same | tail
        · exact same ▸ retained
        · exact valuesAvailable selected tail

/-- Every physical ordinary projection preserves cache facts and complete result payloads. -/
theorem read_available [DecidableEq (EdgeKey Symbol Guard)] (path : Path) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value) : Checked Available (read path value) state := by
  induction path generalizing value state with
  | nil => exact ⟨facts, by intro result same; cases Option.some.inj same; exact available⟩
  | cons index path ih =>
      cases value with
      | empty => exact ⟨facts, by intro result same; cases Option.some.inj same; exact empty_available state⟩
      | node entry edges depth free =>
          have rowFacts := rows_available (read path) ih index edges state facts (by
            intro edge member child present
            exact available.children child (List.mem_flatMap.mpr ⟨edge, member, present⟩))
          exact bindOptional_checked _ _ state ChildrenAvailable Available rowFacts
            (fun values available => union_checked values _ rowFacts.1 available)
      | reference | union | mu => exact ⟨facts, by intro result impossible; cases impossible⟩

end MicroCFTA.EqualityLeafProjectionPathWorker
