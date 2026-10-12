import MicroCFTA.EqualityLeafProjectionUnion

/-!
# Finite-cache compilation of retained occurrence trees

The compiler retains original duplicate and dead ancestor requests. Each
finite completed computation supplies its own common cache. Readback in
that cache agrees with pure lowering of that specific occurrence tree.
No cache is required to contain every possible constructor request.
-/
namespace MicroCFTA.EqualityLeafProjectionCompile
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax
open EqualityLeafProjectionWorkers (sequence sequence_safe workerValue)

/-- Ancestor tags preserve the complete source symbol and constraint. -/
abbrev Tag (Symbol Guard : Type) := Symbol × Guard

/-- Execute every retained ancestor edge request before source node normalization. -/
def node (rows : List (Tag Symbol Guard × List (Value Symbol Guard))) : Work Symbol Guard (Value Symbol Guard) :=
  (sequence (rows.map fun (tag, children) => makeEdge tag.1 tag.2 children)).bind makeNode

mutual
/-- Compile original leaf occurrences and ancestor requests through the actual caches. -/
def compile (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) : Tree (Tag Symbol Guard) Leaf → Work Symbol Guard (Value Symbol Guard)
  | .empty => .pure .empty
  | .leaf value => leaf value
  | .node edges => (compileEdges leaf edges).bind makeNode

/-- Keep duplicate and dead rows until the actual source node constructor. -/
def compileEdges (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) : List (Edge (Tag Symbol Guard) Leaf) → Work Symbol Guard (List (EdgeValue Symbol Guard))
  | [] => .pure []
  | .mk tag children :: rest => (compileForest leaf children).bind fun values =>
      (makeEdge tag.1 tag.2 values).bind fun edge =>
      (compileEdges leaf rest).bind fun edges => .pure (edge :: edges)

/-- Source child order is the original ordered occurrence list. -/
def compileForest (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) : List (Tree (Tag Symbol Guard) Leaf) → Work Symbol Guard (List (Value Symbol Guard))
  | [] => .pure []
  | first :: rest => (compile leaf first).bind fun value =>
      (compileForest leaf rest).bind fun values => .pure (value :: values)
end

/-- A cache snapshot gives local constructor readback and the finite path workers. -/
def snapshot [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) : Source (Tag Symbol Guard) Leaf (Value Symbol Guard) where
  empty := .empty
  leaf value := (run (leaf value) state).1
  node rows := (run (node rows) state).1
  edit edits value := workerValue (EqualityLeafProjectionWorkers.edit meet edits value) state
  require paths value := workerValue (EqualityLeafProjectionWorkers.require paths value) state

/-- A completed bind gives allocation-free replay of both actual component requests. -/
theorem bind_completed [DecidableEq (EdgeKey Symbol Guard)]
    (first : Work Symbol Guard First) (next : First → Work Symbol Guard Result)
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (first.bind next) before).2 after) :
    let middle := run first before
    Grows middle.2 after ∧ run first after = (middle.1, after) ∧
      run (next middle.1) after = ((run (first.bind next) before).1, after) := by
  let middle := run first before
  have checked := InternedConstructorTemplates.run_correct first before valid
  have later := InternedConstructorTemplates.run_correct (next middle.1) middle.2 checked.1
  have finalGrowth : Grows (run (next middle.1) middle.2).2 after := by simpa only [run_bind] using growth
  have earlier := grows_trans later.2 finalGrowth
  refine ⟨earlier, replay first before after valid earlier, ?_⟩
  simpa only [run_bind] using replay (next middle.1) middle.2 after checked.1 finalGrowth

mutual
/-- Pure lowering in a completed cache is exact for this finite original occurrence tree. -/
theorem compile_lower [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (tree : Tree (Tag Symbol Guard) Leaf) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (compile leaf tree) before).2 after) :
    lower (snapshot leaf meet after) tree = (run (compile leaf tree) before).1 := by
  cases tree with
  | empty => rfl
  | leaf value =>
      have result := congrArg (fun result : Value Symbol Guard × State Symbol Guard => result.1)
        (replay (leaf value) before after valid growth)
      exact result
  | node edges =>
      have completed := bind_completed (compileEdges leaf edges) makeNode before after valid growth
      have rows := compileEdges_lower leaf meet edges before after valid completed.1
      change (run (node (lowerEdges (snapshot leaf meet after) edges)) after).1 = _
      rw [node, run_bind, rows]
      have result := congrArg (fun result : Value Symbol Guard × State Symbol Guard => result.1) completed.2.2
      exact result
termination_by sizeOf tree

/-- The completed cache replays all retained ancestor rows with their lowered ordered children. -/
theorem compileEdges_lower [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edges : List (Edge (Tag Symbol Guard) Leaf)) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (compileEdges leaf edges) before).2 after) :
    run (sequence ((lowerEdges (snapshot leaf meet after) edges).map fun (tag, children) => makeEdge tag.1 tag.2 children)) after =
      ((run (compileEdges leaf edges) before).1, after) := by
  cases edges with
  | nil => rfl
  | cons edge rest =>
      cases edge with
      | mk tag children =>
          let childResult := run (compileForest leaf children) before
          let edgeResult := run (makeEdge tag.1 tag.2 childResult.1) childResult.2
          let tailResult := run (compileEdges leaf rest) edgeResult.2
          have childValid : InternedConstructorTemplates.Valid childResult.2 :=
            (InternedConstructorTemplates.run_correct _ before valid).1
          have edgeValid : InternedConstructorTemplates.Valid edgeResult.2 :=
            (InternedConstructorTemplates.run_correct _ childResult.2 childValid).1
          have tailGrowth : Grows tailResult.2 after := by
            simpa only [compileEdges, run_bind, run] using growth
          have edgeGrowth : Grows edgeResult.2 after := grows_trans
            (InternedConstructorTemplates.run_correct _ edgeResult.2 edgeValid).2 tailGrowth
          have childGrowth : Grows childResult.2 after := grows_trans
            (InternedConstructorTemplates.run_correct _ childResult.2 childValid).2 edgeGrowth
          have childrenSame := compileForest_lower leaf meet children before after valid childGrowth
          have edgeReplay := replay (makeEdge tag.1 tag.2 childResult.1) childResult.2 after childValid edgeGrowth
          have tailSame := compileEdges_lower leaf meet rest edgeResult.2 after edgeValid tailGrowth
          change run (makeEdge tag.1 tag.2 (run (compileForest leaf children) before).1) after = (edgeResult.1, after) at edgeReplay
          rw [lowerEdges, List.map_cons, sequence, run_bind, childrenSame, edgeReplay]
          dsimp only
          rw [run_bind, tailSame]
          simp only [run]
          simp only [compileEdges, run_bind, run, childResult, edgeResult]
termination_by sizeOf edges

/-- Every ordered child result has exact snapshot lowering after finite completion. -/
theorem compileForest_lower [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (compileForest leaf forest) before).2 after) :
    lowerForest (snapshot leaf meet after) forest = (run (compileForest leaf forest) before).1 := by
  cases forest with
  | nil => rfl
  | cons first rest =>
      let head := run (compile leaf first) before
      let tail := run (compileForest leaf rest) head.2
      have headValid : InternedConstructorTemplates.Valid head.2 :=
        (InternedConstructorTemplates.run_correct _ before valid).1
      have tailGrowth : Grows tail.2 after := by simpa only [compileForest, run_bind, run] using growth
      have headGrowth : Grows head.2 after := grows_trans
        (InternedConstructorTemplates.run_correct _ head.2 headValid).2 tailGrowth
      have headSame := compile_lower leaf meet first before after valid headGrowth
      have tailSame := compileForest_lower leaf meet rest head.2 after headValid tailGrowth
      simp only [lowerForest, headSame, tailSame, compileForest, run_bind, run]
      rfl
termination_by sizeOf forest
end

mutual
/-- Literal ancestor construction preserves the local cache-field safety checks. -/
theorem compile_safe (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (safe : ∀ value, Safe (leaf value)) (tree : Tree (Tag Symbol Guard) Leaf) : Safe (compile leaf tree) := by
  cases tree with
  | empty => trivial
  | leaf value => exact safe value
  | node edges => exact safe_bind _ _ (compileEdges_safe leaf safe edges) makeNode_safe
termination_by sizeOf tree

/-- Ordered ancestor requests preserve their literal source edge fields. -/
theorem compileEdges_safe (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (safe : ∀ value, Safe (leaf value)) (edges : List (Edge (Tag Symbol Guard) Leaf)) : Safe (compileEdges leaf edges) := by
  cases edges with
  | nil => trivial
  | cons edge rest =>
      cases edge with
      | mk tag children =>
          exact safe_bind _ _ (compileForest_safe leaf safe children) (fun _ =>
            safe_bind _ _ (makeEdge_safe _ _ _) (fun _ =>
            safe_bind _ _ (compileEdges_safe leaf safe rest) (fun _ => trivial)))
termination_by sizeOf edges

/-- Finite child compilation derives cache safety from leaf constructor safety. -/
theorem compileForest_safe (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (safe : ∀ value, Safe (leaf value)) (forest : List (Tree (Tag Symbol Guard) Leaf)) : Safe (compileForest leaf forest) := by
  cases forest with
  | nil => trivial
  | cons first rest => exact safe_bind _ _ (compile_safe leaf safe first) (fun _ =>
      safe_bind _ _ (compileForest_safe leaf safe rest) (fun _ => trivial))
termination_by sizeOf forest
end

/-- Actual finite compilation constructs the snapshot required by exact lowering. -/
theorem completed_forest [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (safe : ∀ value, Safe (leaf value)) (forest : List (Tree (Tag Symbol Guard) Leaf))
    (before : State Symbol Guard) (coherent : Coherent before) :
    let result := run (compileForest leaf forest) before
    Coherent result.2 ∧ Grows before result.2 ∧
      lowerForest (snapshot leaf meet result.2) forest = result.1 ∧
      run (compileForest leaf forest) result.2 = (result.1, result.2) := by
  let result := run (compileForest leaf forest) before
  exact ⟨InternedErasedEdgeReplay.run_coherent _ before (compileForest_safe leaf safe forest) coherent,
    (InternedConstructorTemplates.run_correct _ before coherent.valid).2,
    compileForest_lower leaf meet forest before result.2 coherent.valid (grows_refl result.2),
    replay (compileForest leaf forest) before result.2 coherent.valid (grows_refl result.2)⟩

/-- Equal original occurrence forests produce identical complete physical records
when their two completed runs are retained in a common cache. -/
theorem same_forest [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (meet : Leaf → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (forest : List (Tree (Tag Symbol Guard) Leaf)) (first second after : State Symbol Guard)
    (firstValid : InternedConstructorTemplates.Valid first) (secondValid : InternedConstructorTemplates.Valid second)
    (firstGrowth : Grows (run (compileForest leaf forest) first).2 after)
    (secondGrowth : Grows (run (compileForest leaf forest) second).2 after) :
    (run (compileForest leaf forest) first).1 = (run (compileForest leaf forest) second).1 :=
  (compileForest_lower leaf meet forest first after firstValid firstGrowth).symm.trans
    (compileForest_lower leaf meet forest second after secondValid secondGrowth)

end MicroCFTA.EqualityLeafProjectionCompile
