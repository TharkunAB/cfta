import MicroCFTA.InternedConstructionProvenance

/-!
# Canonical replay after an outer-dependent edge is erased

A changed outer reference can remain in an interned edge whose other child
became EmptyNode. Source node normalization discards that complete edge.
The surviving constructor requests reuse the earlier completed record.
-/
namespace MicroCFTA.InternedErasedEdgeReplay
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedBinderProtocol (NodeRef)
open InternedProbeProvenance

/-- Local constructor-field certification preserves coherence even while unrelated binders are pending. -/
theorem run_coherent [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : InternedConstructorTemplates.State Symbol Guard) (safe : Safe computation) (coherent : Coherent state) :
    Coherent (run computation state).2 := by
  induction computation generalizing state with
  | pure value => exact coherent
  | edge key identify resume ih => exact ih _ _ (safe.2 _) (edgeStep_coherent _ _ _ coherent safe.1)
  | node key identify resume ih => exact ih _ _ (safe.2 _) (nodeStep_coherent _ _ _ coherent safe.1)

/-- Actual edge readback retains exactly its requested ordered child references. -/
theorem makeEdge_references [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) :
    (run (makeEdge symbol constraint values) state).1.children.map Value.referenceOf = values.map Value.referenceOf := by
  have correct := edgeStep_correct ⟨symbol, values.map Value.referenceOf, constraint⟩
    (fun entry => .mk entry values) state coherent.valid
  have after := edgeStep_coherent ⟨symbol, values.map Value.referenceOf, constraint⟩
    (fun entry => .mk entry values) state coherent (fun _ key => ⟨rfl, key, rfl⟩)
  exact (after.edges _ _ correct.2.2).2.2

/-- An interned edge that has an EmptyNode child is removed before parent interning. -/
theorem makeNode_erases (edges : List (EdgeValue Symbol Guard)) (dead : EdgeValue Symbol Guard)
    (emptyChild : .empty ∈ dead.children.map Value.referenceOf) :
    makeNode (edges ++ [dead]) = makeNode edges := by
  have rejected : dead.children.any (fun child => child.referenceOf == .empty) = true := by
    obtain ⟨child, member, same⟩ := List.mem_map.mp emptyChild
    exact List.any_eq_true.mpr ⟨child, member, by simpa only [beq_iff_eq] using same⟩
  simp [makeNode, surviving, List.filter_append, rejected]

/-- Ordered edge compilation retains all source effects before it concatenates the results. -/
theorem compileEdges_append [DecidableEq (EdgeKey Symbol Guard)]
    (left right : List (EdgeTemplate Symbol Guard)) (argument : Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) :
    run (compileEdges (left ++ right) argument) state =
      let first := run (compileEdges left argument) state
      let second := run (compileEdges right argument) first.2
      (first.1 ++ second.1, second.2) := by
  induction left generalizing state with
  | nil => simp [compileEdges, run]
  | cons first rest ih =>
      cases first with
      | mk symbol constraint children =>
          simp only [List.cons_append, compileEdges, run_bind, run, ih, List.cons_append]

/-- Add the exact source edge whose second child has normalized to EmptyNode. -/
def extension (live : List (EdgeTemplate Symbol Guard)) (symbol : Symbol) (constraint : Guard)
    (outer : Value Symbol Guard) : Template Symbol Guard :=
  .node (live ++ [.mk symbol constraint [.captured outer, .captured .empty]])

/-- The extension executes its live children, then the erased edge, then the surviving parent. -/
theorem extension_run [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeTemplate Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (outer argument : Value Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state) :
    run (compile (extension live symbol constraint outer) argument) state =
      let first := run (compileEdges live argument) state
      let erased := run (makeEdge symbol constraint [outer, .empty]) first.2
      run (makeNode first.1) erased.2 := by
  have firstCoherent := run_coherent (compileEdges live argument) state (compileEdges_safe live argument) coherent
  simp only [extension, compile, run_bind, compileEdges_append]
  simp only [compileEdges, compileMany, compile, run_bind, run]
  have emptyChild : NodeRef.empty ∈ (run (makeEdge symbol constraint [outer, .empty])
      (run (compileEdges live argument) state).2).1.children.map Value.referenceOf := by
    rw [makeEdge_references symbol constraint [outer, .empty] _ firstCoherent]
    simp [Value.referenceOf]
  rw [makeNode_erases _ _ emptyChild]

/-- Changed values in an erased edge cannot change the earlier complete surviving record. -/
theorem extension_replay [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeTemplate Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (oldOuter newOuter argument : Value Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (coherentBefore : Coherent before)
    (coherentAfter : Coherent after)
    (growth : Grows (run (compile (extension live symbol constraint oldOuter) argument) before).2 after) :
    (run (compile (extension live symbol constraint newOuter) argument) after).1 =
      (run (compile (extension live symbol constraint oldOuter) argument) before).1 := by
  let first := run (compileEdges live argument) before
  let oldDead := run (makeEdge symbol constraint [oldOuter, .empty]) first.2
  let oldParent := run (makeNode first.1) oldDead.2
  let newDead := run (makeEdge symbol constraint [newOuter, .empty]) after
  have firstCorrect := InternedConstructorTemplates.run_correct (compileEdges live argument) before coherentBefore.valid
  have oldDeadCorrect := InternedConstructorTemplates.run_correct (makeEdge symbol constraint [oldOuter, .empty]) first.2 firstCorrect.1
  have oldParentCorrect := InternedConstructorTemplates.run_correct (makeNode first.1) oldDead.2 oldDeadCorrect.1
  have newDeadCorrect := InternedConstructorTemplates.run_correct (makeEdge symbol constraint [newOuter, .empty]) after coherentAfter.valid
  have beforeEq := extension_run live symbol constraint oldOuter argument before coherentBefore
  have parentGrowth : Grows oldParent.2 after := by simpa only [beforeEq] using growth
  have firstReplay := replay (compileEdges live argument) before after coherentBefore.valid
    (grows_trans oldDeadCorrect.2 (grows_trans oldParentCorrect.2 parentGrowth))
  have afterEq := extension_run live symbol constraint newOuter argument after coherentAfter
  rw [firstReplay] at afterEq
  have parentReplay := replay (makeNode first.1) oldDead.2 newDead.2 oldDeadCorrect.1
    (grows_trans parentGrowth newDeadCorrect.2)
  calc
    _ = (run (makeNode first.1) newDead.2).1 := congrArg Prod.fst afterEq
    _ = oldParent.1 := by simpa only using congrArg Prod.fst parentReplay
    _ = _ := congrArg Prod.fst beforeEq.symm

/-- Exact source self-union normalization preserves replay after the dead edge changes. -/
theorem normalized_replay [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeTemplate Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (oldOuter newOuter : Value Symbol Guard) (name : InternedBinderProtocol.Reference)
    (before after : InternedConstructorTemplates.State Symbol Guard) (coherentBefore : Coherent before)
    (coherentAfter : Coherent after)
    (growth : Grows (run (compileBody (extension live symbol constraint oldOuter) name) before).2 after) :
    (run (compileBody (extension live symbol constraint newOuter) name) after).1 =
      (run (compileBody (extension live symbol constraint oldOuter) name) before).1 := by
  let oldBody := run (compile (extension live symbol constraint oldOuter) (.reference name)) before
  let newBody := run (compile (extension live symbol constraint newOuter) (.reference name)) after
  have oldCorrect := InternedConstructorTemplates.run_correct
    (compile (extension live symbol constraint oldOuter) (.reference name)) before coherentBefore.valid
  have normalizedCorrect := InternedConstructorTemplates.run_correct (withoutSelfReference name oldBody.1) oldBody.2 oldCorrect.1
  have newCorrect := InternedConstructorTemplates.run_correct
    (compile (extension live symbol constraint newOuter) (.reference name)) after coherentAfter.valid
  have normalizedGrowth : Grows (run (withoutSelfReference name oldBody.1) oldBody.2).2 after := by
    simpa only [compileBody, run_bind] using growth
  have same := extension_replay live symbol constraint oldOuter newOuter (.reference name) before after
    coherentBefore coherentAfter (grows_trans normalizedCorrect.2 normalizedGrowth)
  have again := replay (withoutSelfReference name oldBody.1) oldBody.2 newBody.2 oldCorrect.1
    (grows_trans normalizedGrowth newCorrect.2)
  simp only [compileBody, run_bind]
  rw [same]
  simpa only using congrArg Prod.fst again

/-- Both exact Mu key probes reuse the earlier complete records after outer-dependent edge erasure. -/
theorem probes_replay [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeTemplate Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (oldOuter newOuter : Value Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (coherentBefore : Coherent before)
    (coherentAfter : Coherent after)
    (growth : Grows (probes (extension live symbol constraint oldOuter) before).2 after) :
    (probes (extension live symbol constraint newOuter) after).1 =
      (probes (extension live symbol constraint oldOuter) before).1 := by
  let oldTemplate := extension live symbol constraint oldOuter
  let newTemplate := extension live symbol constraint newOuter
  let oldDepth := run (compileBody oldTemplate .depth) before
  let newDepth := run (compileBody newTemplate .depth) after
  have oldDepthCoherent := run_coherent (compileBody oldTemplate .depth) before
    (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _)) coherentBefore
  have ordinaryCorrect := InternedConstructorTemplates.run_correct
    (compileBody oldTemplate (.uninterned oldDepth.1.depth)) oldDepth.2 oldDepthCoherent.valid
  have newDepthCoherent := run_coherent (compileBody newTemplate .depth) after
    (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _)) coherentAfter
  have newDepthGrowth := (InternedConstructorTemplates.run_correct (compileBody newTemplate .depth) after coherentAfter.valid).2
  have depthSame := normalized_replay live symbol constraint oldOuter newOuter .depth before after
    coherentBefore coherentAfter (grows_trans ordinaryCorrect.2 growth)
  have ordinarySame := normalized_replay live symbol constraint oldOuter newOuter (.uninterned oldDepth.1.depth)
    oldDepth.2 newDepth.2 oldDepthCoherent newDepthCoherent (grows_trans growth newDepthGrowth)
  simp only [probes]
  rw [depthSame]
  exact congrArg (fun ordinary => (oldDepth.1, ordinary)) ordinarySame

/-- An earlier completed Mu request is reused even when discarded outer-dependent edges have different keys. -/
theorem completed_probe_readback [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeTemplate Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (oldOuter newOuter : Value Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (coherentBefore : Coherent before)
    (coherentAfter : Coherent after)
    (growth : Grows (internMu (extension live symbol constraint oldOuter) before).2 after) :
    let repeated := probes (extension live symbol constraint newOuter) after
    repeated.2.nodeRecords (muKey repeated.1.1 repeated.1.2) =
      some (internMu (extension live symbol constraint oldOuter) before).1 := by
  let oldTemplate := extension live symbol constraint oldOuter
  let newTemplate := extension live symbol constraint newOuter
  let original := probes oldTemplate before
  let repeated := probes newTemplate after
  have originalCorrect := InternedConstructorTemplates.probes_correct oldTemplate before coherentBefore.valid
  have finalCorrect := InternedConstructorTemplates.finishMu_correct oldTemplate original.1.1 original.1.2 original.2 originalCorrect.1
  have same := probes_replay live symbol constraint oldOuter newOuter before after coherentBefore coherentAfter
    (grows_trans finalCorrect.2 growth)
  have repeatedGrowth := (InternedConstructorTemplates.probes_correct newTemplate after coherentAfter.valid).2
  have stored := (grows_trans growth repeatedGrowth).nodeRecords _ _
    (finishMu_stored oldTemplate original.1.1 original.1.2 original.2)
  change repeated.2.nodeRecords (muKey original.1.1 original.1.2) =
    some (finishMu oldTemplate original.1.1 original.1.2 original.2).1 at stored
  have keySame : muKey repeated.1.1 repeated.1.2 = muKey original.1.1 original.1.2 := congrArg (fun pair => muKey pair.1 pair.2) same
  change repeated.2.nodeRecords (muKey repeated.1.1 repeated.1.2) = _
  rw [keySame]
  exact stored

/-- Changed erased-edge dependencies read back the exact earlier Mu record instead of entering a pending slot. -/
theorem internMu_replay [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeTemplate Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (oldOuter newOuter : Value Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (coherentBefore : Coherent before)
    (coherentAfter : Coherent after)
    (growth : Grows (internMu (extension live symbol constraint oldOuter) before).2 after) :
    (internMu (extension live symbol constraint newOuter) after).1 =
      (internMu (extension live symbol constraint oldOuter) before).1 := by
  have stored := completed_probe_readback live symbol constraint oldOuter newOuter before after coherentBefore coherentAfter growth
  simp only [internMu, finishMu, stored]

/-- Smart cleanup preserves the same complete returned record after erased-edge replay. -/
theorem createMu_replay [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeTemplate Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (oldOuter newOuter : Value Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard) (coherentBefore : Coherent before)
    (coherentAfter : Coherent after)
    (growth : Grows (createMu (extension live symbol constraint oldOuter) before).2 after) :
    (createMu (extension live symbol constraint newOuter) after).1 =
      (createMu (extension live symbol constraint oldOuter) before).1 :=
  congrArg cleanup (internMu_replay live symbol constraint oldOuter newOuter before after coherentBefore coherentAfter growth)

end MicroCFTA.InternedErasedEdgeReplay
