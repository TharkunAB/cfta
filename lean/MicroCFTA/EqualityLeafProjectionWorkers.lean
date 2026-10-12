import MicroCFTA.EqualityLeafProjectionRebuild

/-!
# Physical ordinary-node path workers

These finite workers copy the source ordinary-node edit and required-path
branches. They use the actual edge and node cache requests. A selected
binder, reference, or open union returns none. Unselected positions return
unchanged. Recursive unfolding is outside this fragment. Empty child slots
return immediately without a cache request.
-/
namespace MicroCFTA.EqualityLeafProjectionWorkers
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionSyntax

/-- Stop a finite ordinary worker when a required node is outside its fragment. -/
def bindOptional (work : Work Symbol Guard (Option α)) (next : α → Work Symbol Guard (Option β)) :
    Work Symbol Guard (Option β) := work.bind fun result => match result with
      | none => .pure none
      | some value => next value

/-- Optional failure does not invent a constructor request. -/
theorem bindOptional_safe (work : Work Symbol Guard (Option α)) (next : α → Work Symbol Guard (Option β))
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (bindOptional work next) :=
  safe_bind work _ first (fun result => by cases result with | none => trivial | some value => exact later value)

mutual
  /-- Edit a finite ordinary source node with simultaneous leaf targets. -/
  def edit (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (edits : List (Path × Target)) (value : Value Symbol Guard) : Work Symbol Guard (Option (Value Symbol Guard)) :=
    match edits with
    | [] => .pure (some value)
    | _ :: _ => match value with
      | .empty => .pure (some .empty)
      | .reference _ | .union _ _ _ _ | .mu _ _ _ _ => .pure none
      | .node _ edges _ _ => match atRoot edits with
        | some target => (meet target value).bind (fun result => .pure (some result))
        | none => bindOptional (editEdges meet edits edges) fun results =>
            (makeNode results).bind (fun result => .pure (some result))

  /-- Rebuild the source edge only after all of its selected child edits complete. -/
  def editEdges (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (edits : List (Path × Target)) : List (EdgeValue Symbol Guard) → Work Symbol Guard (Option (List (EdgeValue Symbol Guard)))
    | [] => .pure (some [])
    | .mk entry original :: rest =>
        bindOptional (editChildren meet edits 0 original) fun children =>
          (makeEdge entry.key.symbol entry.key.constraint children).bind fun result =>
            bindOptional (editEdges meet edits rest) fun results => .pure (some (result :: results))

  /-- Child position lookup uses the unchanged original order. -/
  def editChildren (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (edits : List (Path × Target)) (index : Nat) :
      List (Value Symbol Guard) → Work Symbol Guard (Option (List (Value Symbol Guard)))
    | [] => .pure (some [])
    | child :: rest =>
        bindOptional (edit meet (descendEdits edits index) child) fun result =>
          bindOptional (editChildren meet edits (index + 1) rest) fun results => .pure (some (result :: results))
end

mutual
  /-- Require actual child positions before any equality intersection runs. -/
  def require (paths : List Path) (value : Value Symbol Guard) : Work Symbol Guard (Option (Value Symbol Guard)) :=
    if fits paths 0 then .pure (some value) else
      match value with
      | .empty => .pure (some .empty)
      | .reference _ | .union _ _ _ _ | .mu _ _ _ _ => .pure none
      | .node _ edges _ _ => bindOptional (requireEdges paths edges) fun results =>
          (makeNode results).bind (fun result => .pure (some result))

  /-- A required missing child removes its source edge before child recursion. -/
  def requireEdges (paths : List Path) : List (EdgeValue Symbol Guard) → Work Symbol Guard (Option (List (EdgeValue Symbol Guard)))
    | [] => .pure (some [])
    | .mk entry original :: rest =>
        if fits paths original.length then
          bindOptional (requireChildren paths 0 original) fun children =>
            (makeEdge entry.key.symbol entry.key.constraint children).bind fun result =>
              bindOptional (requireEdges paths rest) fun results => .pure (some (result :: results))
        else requireEdges paths rest

  /-- Required-path suffixes retain the original child position. -/
  def requireChildren (paths : List Path) (index : Nat) :
      List (Value Symbol Guard) → Work Symbol Guard (Option (List (Value Symbol Guard)))
    | [] => .pure (some [])
    | child :: rest => bindOptional (require (descend paths index) child) fun result =>
        bindOptional (requireChildren paths (index + 1) rest) fun results => .pure (some (result :: results))
end

/-- Empty source nodes absorb every selected edit without allocation. -/
theorem edit_empty (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) : edit meet edits .empty = .pure (some .empty) := by
  cases edits <;> rfl

/-- Required paths never resurrect an empty node or allocate a replacement. -/
theorem require_empty (paths : List Path) : require (Symbol := Symbol) (Guard := Guard) paths .empty = .pure (some .empty) := by
  unfold require
  split <;> rfl

/-- Unselected child positions return their existing complete source record. -/
theorem edit_unselected (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (value : Value Symbol Guard) : edit meet [] value = .pure (some value) := by simp only [edit]

/-- An empty requirement trie returns the original record directly. -/
theorem require_unselected (value : Value Symbol Guard) : require [] value = .pure (some value) := by cases value <;> simp [require, fits]

mutual
  /-- Every edit request retains the source key and metadata construction rules. -/
  theorem edit_safe (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (meetSafe : ∀ target value, Safe (meet target value)) (edits : List (Path × Target)) (value : Value Symbol Guard) :
      Safe (edit meet edits value) := by
    cases edits with
    | nil => simp only [edit]; trivial
    | cons selected rest =>
        cases value <;> simp only [edit]
        all_goals first
          | trivial
          | (split
             · exact safe_bind _ _ (meetSafe _ _) (fun _ => trivial)
             · exact bindOptional_safe _ _ (editEdges_safe meet meetSafe _ _)
                 (fun values => safe_bind _ _ (makeNode_safe values) (fun _ => trivial)))

  /-- Source edge requests remain safe after all recursive child edits. -/
  theorem editEdges_safe (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (meetSafe : ∀ target value, Safe (meet target value)) (edits : List (Path × Target))
      (edges : List (EdgeValue Symbol Guard)) : Safe (editEdges meet edits edges) := by
    cases edges with
    | nil => trivial
    | cons edge rest =>
        cases edge with
        | mk entry original =>
            exact bindOptional_safe _ _ (editChildren_safe meet meetSafe edits 0 original) (fun children =>
              safe_bind _ _ (makeEdge_safe _ _ children) (fun _ =>
                bindOptional_safe _ _ (editEdges_safe meet meetSafe edits rest) (fun _ => trivial)))

  /-- Ordered child editing introduces no unverified cache request. -/
  theorem editChildren_safe (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
      (meetSafe : ∀ target value, Safe (meet target value)) (edits : List (Path × Target)) (index : Nat)
      (children : List (Value Symbol Guard)) : Safe (editChildren meet edits index children) := by
    cases children with
    | nil => trivial
    | cons child rest => exact bindOptional_safe _ _ (edit_safe meet meetSafe _ child) (fun _ =>
        bindOptional_safe _ _ (editChildren_safe meet meetSafe edits (index + 1) rest) (fun _ => trivial))
end

mutual
  /-- Required-path recursion uses only the existing safe constructor operations. -/
  theorem require_safe (paths : List Path) (value : Value Symbol Guard) : Safe (require paths value) := by
    unfold require
    split
    · trivial
    · cases value
      all_goals first
        | trivial
        | exact bindOptional_safe _ _ (requireEdges_safe paths _) (fun edges =>
            safe_bind _ _ (makeNode_safe edges) (fun _ => trivial))

  /-- Arity rejection has no child or edge effects. Every retained row uses makeEdge. -/
  theorem requireEdges_safe (paths : List Path) (edges : List (EdgeValue Symbol Guard)) : Safe (requireEdges paths edges) := by
    cases edges with
    | nil => trivial
    | cons edge rest =>
        cases edge with
        | mk entry original =>
            unfold requireEdges
            split
            · exact bindOptional_safe _ _ (requireChildren_safe paths 0 original) (fun children =>
                safe_bind _ _ (makeEdge_safe _ _ children) (fun _ =>
                  bindOptional_safe _ _ (requireEdges_safe paths rest) (fun _ => trivial)))
            · exact requireEdges_safe paths rest

  /-- Each finite child requirement retains all source cache invariants. -/
  theorem requireChildren_safe (paths : List Path) (index : Nat) (children : List (Value Symbol Guard)) :
      Safe (requireChildren paths index children) := by
    cases children with
    | nil => trivial
    | cons child rest => exact bindOptional_safe _ _ (require_safe _ child) (fun _ =>
        bindOptional_safe _ _ (requireChildren_safe paths (index + 1) rest) (fun _ => trivial))
end

/-- Actual finite edit execution preserves complete record coherence, including failure outside the fragment. -/
theorem edit_coherent [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (meetSafe : ∀ target value, Safe (meet target value)) (edits : List (Path × Target))
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) :
    Coherent (run (edit meet edits value) state).2 :=
  InternedErasedEdgeReplay.run_coherent _ state (edit_safe meet meetSafe edits value) coherent

/-- Required-path execution derives coherence without an extra row-operation contract. -/
theorem require_coherent [DecidableEq (EdgeKey Symbol Guard)] (paths : List Path)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) :
    Coherent (run (require paths value) state).2 :=
  InternedErasedEdgeReplay.run_coherent _ state (require_safe paths value) coherent

end MicroCFTA.EqualityLeafProjectionWorkers
