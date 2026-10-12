import MicroCFTA.EqualityLeafProjectionLeafWorkers

/-!
# Finite-cache readback of recursive parent edits

A completed physical worker supplies one cache that retains every child
request and rebuilt edge. The actual parent result can then use these
allocation-free child readbacks in original source position order.
-/
namespace MicroCFTA.EqualityLeafProjectionWorkerReadback
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Path mapChildren descendEdits descend fits)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical

/-- Completed ordered child edits equal the map of their actual snapshot readbacks. -/
theorem editChildren_readback [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (index : Nat) (children : List (Value Symbol Guard))
    (ordinary : OrdinaryChildren children) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (editChildren meet edits index children) before).2 after) :
    (run (editChildren meet edits index children) before).1 =
      some (mapChildren (editedChild meet edits after) index children) := by
  induction children generalizing index before with
  | nil => rfl
  | cons child rest ih =>
      let head := run (edit meet (descendEdits edits index) child) before
      obtain ⟨value, found⟩ := edit_returns meet (descendEdits edits index) child ordinary.1 before
      let tail := run (editChildren meet edits (index + 1) rest) head.2
      have headValid : InternedConstructorTemplates.Valid head.2 :=
        (InternedConstructorTemplates.run_correct _ before valid).1
      obtain ⟨values, tailFound⟩ := editChildren_returns meet edits (index + 1) rest ordinary.2 head.2
      dsimp only [head] at tailFound
      have tailGrowth : Grows tail.2 after := by
        simpa only [editChildren, bindOptional, run_bind, found, tailFound, run] using growth
      have headGrowth : Grows head.2 after := grows_trans
        (InternedConstructorTemplates.run_correct _ head.2 headValid).2 tailGrowth
      have repeated := replay (edit meet (descendEdits edits index) child) before after valid headGrowth
      have headRead : editedChild meet edits after index child = value := by
        simp only [editedChild, workerValue, repeated, found, Option.getD_some]
      have tailRead := ih (index + 1) ordinary.2 head.2 headValid tailGrowth
      have valuesSame : values = mapChildren (editedChild meet edits after) (index + 1) rest :=
        Option.some.inj (tailFound.symm.trans tailRead)
      simp only [editChildren, bindOptional, run_bind, found, tailFound, run, mapChildren, headRead, ← valuesSame]

/-- Completed physical edge edits equal rebuilding each original edge from the
actual child readbacks in the common cache. -/
theorem editEdges_readback [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (edges : List (EdgeValue Symbol Guard))
    (ordinary : OrdinaryEdges edges) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (editEdges meet edits edges) before).2 after) :
    (run (editEdges meet edits edges) before).1 =
      some (edges.map (rebuild after (editedChild meet edits after))) := by
  induction edges generalizing before with
  | nil => rfl
  | cons edge rest ih =>
      cases edge with
      | mk entry children =>
          let childResult := run (editChildren meet edits 0 children) before
          obtain ⟨values, found⟩ := editChildren_returns meet edits 0 children ordinary.1 before
          let edgeResult := run (makeEdge entry.key.symbol entry.key.constraint values) childResult.2
          let tailResult := run (editEdges meet edits rest) edgeResult.2
          have childValid : InternedConstructorTemplates.Valid childResult.2 :=
            (InternedConstructorTemplates.run_correct _ before valid).1
          have edgeValid : InternedConstructorTemplates.Valid edgeResult.2 :=
            (InternedConstructorTemplates.run_correct _ childResult.2 childValid).1
          obtain ⟨tail, tailFound⟩ := editEdges_returns meet edits rest ordinary.2 edgeResult.2
          dsimp only [edgeResult, childResult] at tailFound
          have tailGrowth : Grows tailResult.2 after := by
            simpa only [editEdges, bindOptional, run_bind, found, tailFound, run] using growth
          have edgeGrowth : Grows edgeResult.2 after := grows_trans
            (InternedConstructorTemplates.run_correct _ edgeResult.2 edgeValid).2 tailGrowth
          have childGrowth : Grows childResult.2 after := grows_trans
            (InternedConstructorTemplates.run_correct _ childResult.2 childValid).2 edgeGrowth
          have childrenRead := editChildren_readback meet edits 0 children ordinary.1 before after valid childGrowth
          have valuesSame : values = mapChildren (editedChild meet edits after) 0 children :=
            Option.some.inj (found.symm.trans childrenRead)
          have repeated := replay (makeEdge entry.key.symbol entry.key.constraint values) childResult.2 after childValid edgeGrowth
          have edgeSame : rebuild after (editedChild meet edits after) (.mk entry children) = edgeResult.1 := by
            change (run (makeEdge entry.key.symbol entry.key.constraint (mapChildren (editedChild meet edits after) 0 children)) after).1 = _
            rw [← valuesSame, repeated]
          have tailRead := ih ordinary.2 edgeResult.2 edgeValid tailGrowth
          have tailSame : tail = rest.map (rebuild after (editedChild meet edits after)) :=
            Option.some.inj (tailFound.symm.trans tailRead)
          simp only [editEdges, bindOptional, run_bind, found, tailFound, run, List.map_cons, edgeSame, ← tailSame]
          rfl

/-- The actual edited parent reconstructs the source's canonical rows from
completed child readbacks. No parent worker equation is assumed. -/
theorem edit_node_readback [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (first : Path × Target) (rest : List (Path × Target))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (ordinary : OrdinaryEdges edges) (noRoot : EqualityLeafProjectionSyntax.atRoot (first :: rest) = none)
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (edit meet (first :: rest) (.node entry edges depth free)) before).2 after) :
    (run (edit meet (first :: rest) (.node entry edges depth free)) before).1 =
      some (run (makeNode (edges.map (rebuild after (editedChild meet (first :: rest) after)))) after).1 := by
  let edited := run (editEdges meet (first :: rest) edges) before
  obtain ⟨rows, found⟩ := editEdges_returns meet (first :: rest) edges ordinary before
  have editedValid : InternedConstructorTemplates.Valid edited.2 :=
    (InternedConstructorTemplates.run_correct _ before valid).1
  have nodeGrowth : Grows (run (makeNode rows) edited.2).2 after := by
    simpa only [edit, noRoot, bindOptional, run_bind, found, run] using growth
  have edgeGrowth : Grows edited.2 after := grows_trans
    (InternedConstructorTemplates.run_correct _ edited.2 editedValid).2 nodeGrowth
  have readback := editEdges_readback meet (first :: rest) edges ordinary before after valid edgeGrowth
  have rowsSame : rows = edges.map (rebuild after (editedChild meet (first :: rest) after)) :=
    Option.some.inj (found.symm.trans readback)
  have repeated := replay (makeNode rows) edited.2 after editedValid nodeGrowth
  rw [← rowsSame, repeated]
  simp only [edit, noRoot, bindOptional, run_bind, found, run]
  rfl


/-- Completed ordered child requirements equal the map of their actual snapshot readbacks. -/
theorem requireChildren_readback [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (index : Nat) (children : List (Value Symbol Guard))
    (ordinary : OrdinaryChildren children) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (requireChildren paths index children) before).2 after) :
    (run (requireChildren paths index children) before).1 =
      some (mapChildren (requiredChild paths after) index children) := by
  induction children generalizing index before with
  | nil => rfl
  | cons child rest ih =>
      let head := run (require (descend paths index) child) before
      obtain ⟨value, found⟩ := require_returns (descend paths index) child ordinary.1 before
      let tail := run (requireChildren paths (index + 1) rest) head.2
      have headValid : InternedConstructorTemplates.Valid head.2 :=
        (InternedConstructorTemplates.run_correct _ before valid).1
      obtain ⟨values, tailFound⟩ := requireChildren_returns paths (index + 1) rest ordinary.2 head.2
      dsimp only [head] at tailFound
      have tailGrowth : Grows tail.2 after := by
        simpa only [requireChildren, bindOptional, run_bind, found, tailFound, run] using growth
      have headGrowth : Grows head.2 after := grows_trans
        (InternedConstructorTemplates.run_correct _ head.2 headValid).2 tailGrowth
      have repeated := replay (require (descend paths index) child) before after valid headGrowth
      have headRead : requiredChild paths after index child = value := by
        simp only [requiredChild, workerValue, repeated, found, Option.getD_some]
      have tailRead := ih (index + 1) ordinary.2 head.2 headValid tailGrowth
      have valuesSame : values = mapChildren (requiredChild paths after) (index + 1) rest :=
        Option.some.inj (tailFound.symm.trans tailRead)
      simp only [requireChildren, bindOptional, run_bind, found, tailFound, run, mapChildren, headRead, ← valuesSame]

/-- Required-path filtering keeps the original arity decision before snapshot rebuilding. -/
theorem requireEdges_readback [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (edges : List (EdgeValue Symbol Guard))
    (ordinary : OrdinaryEdges edges) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (requireEdges paths edges) before).2 after) :
    (run (requireEdges paths edges) before).1 =
      some ((edges.filter (fun edge => fits paths edge.children.length)).map (rebuild after (requiredChild paths after))) := by
  induction edges generalizing before with
  | nil => rfl
  | cons edge rest ih =>
      cases edge with
      | mk entry children =>
          by_cases accepted : fits paths children.length = true
          · let childResult := run (requireChildren paths 0 children) before
            obtain ⟨values, found⟩ := requireChildren_returns paths 0 children ordinary.1 before
            let edgeResult := run (makeEdge entry.key.symbol entry.key.constraint values) childResult.2
            let tailResult := run (requireEdges paths rest) edgeResult.2
            have childValid : InternedConstructorTemplates.Valid childResult.2 :=
              (InternedConstructorTemplates.run_correct _ before valid).1
            have edgeValid : InternedConstructorTemplates.Valid edgeResult.2 :=
              (InternedConstructorTemplates.run_correct _ childResult.2 childValid).1
            obtain ⟨tail, tailFound⟩ := requireEdges_returns paths rest ordinary.2 edgeResult.2
            dsimp only [edgeResult, childResult] at tailFound
            have tailGrowth : Grows tailResult.2 after := by
              simpa only [requireEdges, accepted, ↓reduceIte, bindOptional, run_bind, found, tailFound, run] using growth
            have edgeGrowth : Grows edgeResult.2 after := grows_trans
              (InternedConstructorTemplates.run_correct _ edgeResult.2 edgeValid).2 tailGrowth
            have childGrowth : Grows childResult.2 after := grows_trans
              (InternedConstructorTemplates.run_correct _ childResult.2 childValid).2 edgeGrowth
            have childrenRead := requireChildren_readback paths 0 children ordinary.1 before after valid childGrowth
            have valuesSame : values = mapChildren (requiredChild paths after) 0 children :=
              Option.some.inj (found.symm.trans childrenRead)
            have repeated := replay (makeEdge entry.key.symbol entry.key.constraint values) childResult.2 after childValid edgeGrowth
            have edgeSame : rebuild after (requiredChild paths after) (.mk entry children) = edgeResult.1 := by
              change (run (makeEdge entry.key.symbol entry.key.constraint (mapChildren (requiredChild paths after) 0 children)) after).1 = _
              rw [← valuesSame, repeated]
            have tailRead := ih ordinary.2 edgeResult.2 edgeValid tailGrowth
            have tailSame : tail = (rest.filter (fun edge => fits paths edge.children.length)).map (rebuild after (requiredChild paths after)) :=
              Option.some.inj (tailFound.symm.trans tailRead)
            have keep : ((EdgeValue.mk entry children :: rest).filter (fun edge => fits paths edge.children.length)) =
                EdgeValue.mk entry children :: rest.filter (fun edge => fits paths edge.children.length) := by
              rw [List.filter_cons]
              exact ite_eq_left accepted
            simp only [requireEdges, accepted, ↓reduceIte, bindOptional, run_bind, found, tailFound, run,
              keep, List.map_cons, edgeSame, ← tailSame]
            rfl
          · have rejected : fits paths children.length = false := Bool.eq_false_iff.mpr accepted
            simp only [requireEdges, rejected, Bool.false_eq_true, ↓reduceIte] at growth ⊢
            simp only [List.filter_cons, EdgeValue.children, rejected, Bool.false_eq_true, ↓reduceIte]
            exact ih ordinary.2 before valid growth

/-- Proper required paths reconstruct the canonical parent from exactly the
original-arity rows that survive and their completed child requirements. -/
theorem require_node_readback [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (proper : fits paths 0 = false)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (ordinary : OrdinaryEdges edges) (before after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growth : Grows (run (require paths (.node entry edges depth free)) before).2 after) :
    (run (require paths (.node entry edges depth free)) before).1 =
      some (run (makeNode ((edges.filter (fun edge => fits paths edge.children.length)).map
        (rebuild after (requiredChild paths after)))) after).1 := by
  let required := run (requireEdges paths edges) before
  obtain ⟨rows, found⟩ := requireEdges_returns paths edges ordinary before
  have requiredValid : InternedConstructorTemplates.Valid required.2 :=
    (InternedConstructorTemplates.run_correct _ before valid).1
  have nodeGrowth : Grows (run (makeNode rows) required.2).2 after := by
    simpa only [require, proper, Bool.false_eq_true, ↓reduceIte, bindOptional, run_bind, found, run] using growth
  have edgeGrowth : Grows required.2 after := grows_trans
    (InternedConstructorTemplates.run_correct _ required.2 requiredValid).2 nodeGrowth
  have readback := requireEdges_readback paths edges ordinary before after valid edgeGrowth
  have rowsSame : rows = (edges.filter (fun edge => fits paths edge.children.length)).map (rebuild after (requiredChild paths after)) :=
    Option.some.inj (found.symm.trans readback)
  have repeated := replay (makeNode rows) required.2 after requiredValid nodeGrowth
  rw [← rowsSame, repeated]
  simp only [require, proper, Bool.false_eq_true, ↓reduceIte, bindOptional, run_bind, found, run]
  rfl

end MicroCFTA.EqualityLeafProjectionWorkerReadback
