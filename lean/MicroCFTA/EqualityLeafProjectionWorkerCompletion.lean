import MicroCFTA.EqualityLeafProjectionWorkers

/-!
# Completion of physical ordinary path workers

Finite ordinary input records contain no binder, free reference, or open
union below their ancestor rows. The copied path workers therefore return
a result on every such input. No source completion contract is required.
-/
namespace MicroCFTA.EqualityLeafProjectionWorkers
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionSyntax

mutual
  /-- The selected source fragment contains only finite ordinary constructors. -/
  def Ordinary : Value Symbol Guard → Prop
    | .empty => True
    | .node _ edges _ _ => OrdinaryEdges edges
    | _ => False

  /-- Every child record of every ordinary source edge lies in the same finite fragment. -/
  def OrdinaryEdges : List (EdgeValue Symbol Guard) → Prop
    | [] => True
    | .mk _ children :: rest => OrdinaryChildren children ∧ OrdinaryEdges rest

  /-- Child position order retains the fragment invariant. -/
  def OrdinaryChildren : List (Value Symbol Guard) → Prop
    | [] => True
    | child :: rest => Ordinary child ∧ OrdinaryChildren rest
end

/-- A physical worker completes instead of reaching an unsupported constructor. -/
def Returns [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard (Option α)) (state : State Symbol Guard) : Prop :=
  ∃ value, (run work state).1 = some value

/-- A pure successful result completes immediately. -/
theorem pure_returns [DecidableEq (EdgeKey Symbol Guard)] (value : α) (state : State Symbol Guard) :
    Returns (.pure (some value) : Work Symbol Guard (Option α)) state := ⟨value, rfl⟩

/-- The complete result from the first worker selects the actual following cache state. -/
theorem bindOptional_returns [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard (Option α))
    (next : α → Work Symbol Guard (Option β)) (state : State Symbol Guard)
    (first : Returns work state) (later : ∀ value current, Returns (next value) current) : Returns (bindOptional work next) state := by
  obtain ⟨value, found⟩ := first
  simpa only [Returns, bindOptional, run_bind, found] using later value (run work state).2

/-- A concrete constructor request always continues in its returned cache state. -/
theorem bind_returns [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard α)
    (next : α → Work Symbol Guard (Option β)) (state : State Symbol Guard)
    (later : ∀ value current, Returns (next value) current) : Returns (work.bind next) state := by
  simpa only [Returns, run_bind] using later (run work state).1 (run work state).2

mutual
  /-- Every finite ordinary edit completes using the actual leaf intersection request. -/
  theorem edit_returns [DecidableEq (EdgeKey Symbol Guard)]
      (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (edits : List (Path × Target)) (value : Value Symbol Guard) (ordinary : Ordinary value) (state : State Symbol Guard) :
      Returns (edit meet edits value) state := by
    cases edits with
    | nil => simpa only [edit_unselected] using pure_returns value state
    | cons selected rest =>
        cases value with
        | empty => simpa only [edit_empty] using pure_returns (.empty : Value Symbol Guard) state
        | reference | union | mu => exact False.elim ordinary
        | node entry edges depth free =>
            simp only [edit]
            split
            · exact bind_returns _ _ state (fun value current => pure_returns value current)
            · exact bindOptional_returns _ _ state (editEdges_returns meet _ edges ordinary state)
                (fun values current => bind_returns _ _ current (fun value next => pure_returns value next))

  /-- An ordinary ancestor edge list completes after all selected child edits. -/
  theorem editEdges_returns [DecidableEq (EdgeKey Symbol Guard)]
      (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (edits : List (Path × Target)) (edges : List (EdgeValue Symbol Guard)) (ordinary : OrdinaryEdges edges)
      (state : State Symbol Guard) : Returns (editEdges meet edits edges) state := by
    cases edges with
    | nil => exact pure_returns [] state
    | cons edge rest =>
        cases edge with
        | mk entry children =>
            exact bindOptional_returns _ _ state (editChildren_returns meet edits 0 children ordinary.1 state)
              (fun children current => bind_returns _ _ current (fun edge next =>
                bindOptional_returns _ _ next (editEdges_returns meet edits rest ordinary.2 next)
                  (fun edges final => pure_returns (edge :: edges) final)))

  /-- Every existing ordinary child completes at its original path index. -/
  theorem editChildren_returns [DecidableEq (EdgeKey Symbol Guard)]
      (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (edits : List (Path × Target)) (index : Nat) (children : List (Value Symbol Guard)) (ordinary : OrdinaryChildren children)
      (state : State Symbol Guard) : Returns (editChildren meet edits index children) state := by
    cases children with
    | nil => exact pure_returns [] state
    | cons child rest =>
        exact bindOptional_returns _ _ state (edit_returns meet _ child ordinary.1 state)
          (fun value current => bindOptional_returns _ _ current (editChildren_returns meet edits (index + 1) rest ordinary.2 current)
            (fun values final => pure_returns (value :: values) final))
end

mutual
  /-- Required-path filtering always completes on a finite ordinary source record. -/
  theorem require_returns [DecidableEq (EdgeKey Symbol Guard)] (paths : List Path)
      (value : Value Symbol Guard) (ordinary : Ordinary value) (state : State Symbol Guard) : Returns (require paths value) state := by
    unfold require
    split
    · exact pure_returns value state
    · cases value with
      | empty => exact pure_returns (Value.empty : Value Symbol Guard) state
      | reference | union | mu => exact False.elim ordinary
      | node entry edges depth free =>
          exact bindOptional_returns _ _ state (requireEdges_returns paths edges ordinary state)
            (fun edges current => bind_returns _ _ current (fun value next => pure_returns value next))

  /-- Required missing children delete a row without executing its descendants. -/
  theorem requireEdges_returns [DecidableEq (EdgeKey Symbol Guard)] (paths : List Path)
      (edges : List (EdgeValue Symbol Guard)) (ordinary : OrdinaryEdges edges) (state : State Symbol Guard) :
      Returns (requireEdges paths edges) state := by
    cases edges with
    | nil => exact pure_returns [] state
    | cons edge rest =>
        cases edge with
        | mk entry children =>
            unfold requireEdges
            split
            · exact bindOptional_returns _ _ state (requireChildren_returns paths 0 children ordinary.1 state)
                (fun values current => bind_returns _ _ current (fun edge next =>
                  bindOptional_returns _ _ next (requireEdges_returns paths rest ordinary.2 next)
                    (fun edges final => pure_returns (edge :: edges) final)))
            · exact requireEdges_returns paths rest ordinary.2 state

  /-- Each retained child requirement completes in the actual preceding cache state. -/
  theorem requireChildren_returns [DecidableEq (EdgeKey Symbol Guard)] (paths : List Path) (index : Nat)
      (children : List (Value Symbol Guard)) (ordinary : OrdinaryChildren children) (state : State Symbol Guard) :
      Returns (requireChildren paths index children) state := by
    cases children with
    | nil => exact pure_returns [] state
    | cons child rest =>
        exact bindOptional_returns _ _ state (require_returns _ child ordinary.1 state)
          (fun value current => bindOptional_returns _ _ current (requireChildren_returns paths (index + 1) rest ordinary.2 current)
            (fun values final => pure_returns (value :: values) final))
end

/-- The actual returned edit value preserves coherence and every earlier cache entry. -/
theorem edit_completes [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (meetSafe : ∀ target value, Safe (meet target value)) (edits : List (Path × Target))
    (value : Value Symbol Guard) (ordinary : Ordinary value) (state : State Symbol Guard) (coherent : Coherent state) :
    ∃ result final, run (edit meet edits value) state = (some result, final) ∧ Coherent final ∧ Grows state final := by
  obtain ⟨result, present⟩ := edit_returns meet edits value ordinary state
  refine ⟨result, (run (edit meet edits value) state).2, ?_, edit_coherent meet meetSafe edits value state coherent,
    (InternedConstructorTemplates.run_correct _ state coherent.valid).2⟩
  exact Prod.ext present rfl

/-- Finite required-path execution needs no supplied completion or stability contract. -/
theorem require_completes [DecidableEq (EdgeKey Symbol Guard)] (paths : List Path)
    (value : Value Symbol Guard) (ordinary : Ordinary value) (state : State Symbol Guard) (coherent : Coherent state) :
    ∃ result final, run (require paths value) state = (some result, final) ∧ Coherent final ∧ Grows state final := by
  obtain ⟨result, present⟩ := require_returns paths value ordinary state
  refine ⟨result, (run (require paths value) state).2, ?_, require_coherent paths value state coherent,
    (InternedConstructorTemplates.run_correct _ state coherent.valid).2⟩
  exact Prod.ext present rfl

end MicroCFTA.EqualityLeafProjectionWorkers
