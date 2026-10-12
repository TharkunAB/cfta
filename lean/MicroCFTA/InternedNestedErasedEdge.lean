import MicroCFTA.InternedNestedOrdinary

/-!
# Erased enclosing dependencies in actual nested source execution

The inner source body reads its enclosing variable in an edge that also
has an empty child. Both probes execute that edge request. Node construction
then removes it and reuses the earlier complete inner binder record.
-/
namespace MicroCFTA.InternedNestedErasedEdge
open InternedConstructorTemplates InternedNestedConstruction InternedNestedOrdinary
open InternedStagedBinders (Skeleton EdgeSkeleton instantiate instantiateMany instantiateEdges)
open InternedRecordCoherence InternedErasedEdgeReplay

mutual
/-- Reserve capture slot zero for the enclosing variable that the dead edge reads. -/
def shift : Skeleton Symbol Guard → Skeleton Symbol Guard
  | .argument => .argument
  | .capture index => .capture (index + 1)
  | .node edges => .node (shiftEdges edges)
  | .union members => .union (shiftMany members)
termination_by expression => sizeOf expression

/-- Shift every capture slot in ordered child expressions. -/
def shiftMany : List (Skeleton Symbol Guard) → List (Skeleton Symbol Guard)
  | [] => []
  | first :: rest => shift first :: shiftMany rest
termination_by expressions => sizeOf expressions

/-- Shift captures without changing any source edge declaration. -/
def shiftEdges : List (EdgeSkeleton Symbol Guard) → List (EdgeSkeleton Symbol Guard)
  | [] => []
  | .mk symbol constraint children :: rest => .mk symbol constraint (shiftMany children) :: shiftEdges rest
termination_by expressions => sizeOf expressions
end

mutual
/-- Shifted live syntax reads exactly its original enclosing captures. -/
theorem instantiate_shift (expression : Skeleton Symbol Guard) (outer : Value Symbol Guard)
    (captures : List (Value Symbol Guard)) :
    instantiate (shift expression) (outer :: captures) = instantiate expression captures := by
  cases expression with
  | argument => simp [shift, instantiate]
  | capture index => simp [shift, instantiate]
  | node edges => simp only [shift, instantiate, instantiateEdges_shift edges outer captures]
  | union members => simp only [shift, instantiate, instantiateMany_shift members outer captures]
termination_by sizeOf expression

/-- Capture shifting leaves the exact ordered instantiated children unchanged. -/
theorem instantiateMany_shift (expressions : List (Skeleton Symbol Guard)) (outer : Value Symbol Guard)
    (captures : List (Value Symbol Guard)) :
    instantiateMany (shiftMany expressions) (outer :: captures) = instantiateMany expressions captures := by
  cases expressions with
  | nil => simp [shiftMany, instantiateMany]
  | cons first rest => simp only [shiftMany, instantiateMany, instantiate_shift first outer captures,
      instantiateMany_shift rest outer captures]
termination_by sizeOf expressions

/-- Capture shifting leaves the complete live edge templates unchanged. -/
theorem instantiateEdges_shift (expressions : List (EdgeSkeleton Symbol Guard)) (outer : Value Symbol Guard)
    (captures : List (Value Symbol Guard)) :
    instantiateEdges (shiftEdges expressions) (outer :: captures) = instantiateEdges expressions captures := by
  cases expressions with
  | nil => simp [shiftEdges, instantiateEdges]
  | cons first rest =>
      cases first with
      | mk symbol constraint children => simp only [shiftEdges, instantiateEdges,
          instantiateMany_shift children outer captures, instantiateEdges_shift rest outer captures]
termination_by sizeOf expressions
end

/-- Ordered edge instantiation preserves concatenation. -/
theorem instantiateEdges_append (left right : List (EdgeSkeleton Symbol Guard))
    (captures : List (Value Symbol Guard)) :
    instantiateEdges (left ++ right) captures = instantiateEdges left captures ++ instantiateEdges right captures := by
  induction left with
  | nil => simp [instantiateEdges]
  | cons first rest ih =>
      cases first
      simp only [List.cons_append, instantiateEdges, ih]

/-- Actual empty source syntax and a captured empty value have the same ordinary computation. -/
theorem empty_compile (argument : Value Symbol Guard) :
    compile (.node [] : Template Symbol Guard) argument = compile (.captured .empty) argument := by
  simp [compile, compileEdges, Work.bind, makeNode, canonicalEdges, surviving,
    EnumerationBuilderCaches.canonicalIds]

/-- The exact source extension retains an enclosing-variable read before its empty-child edge is discarded. -/
def body (live : List (EdgeSkeleton Symbol Guard)) (symbol : Symbol) (constraint : Guard) : Skeleton Symbol Guard :=
  .node (shiftEdges live ++ [.mk symbol constraint [.capture 0, .node []]])

/-- The prepared source body uses the same finite work as the already verified erased-edge template. -/
theorem body_compile (live : List (EdgeSkeleton Symbol Guard)) (symbol : Symbol) (constraint : Guard)
    (outer argument : Value Symbol Guard) (captures : List (Value Symbol Guard)) :
    compile (instantiate (body live symbol constraint) (outer :: captures)) argument =
      compile (extension (instantiateEdges live captures) symbol constraint outer) argument := by
  simp only [body, instantiate, instantiateEdges_append, instantiateEdges_shift,
    instantiateEdges, instantiateMany, List.getElem?_cons_zero, Option.getD_some, extension, compile]
  congr 1
  induction instantiateEdges live captures with
  | nil => simp only [List.nil_append, compileEdges, compileMany, empty_compile]
  | cons first rest ih =>
      cases first
      simp only [List.cons_append, compileEdges, ih]

/-- Every normalized probe and fresh callback matches the finite erased-edge computation exactly. -/
theorem body_callback [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeSkeleton Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (outer : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (name : InternedBinderProtocol.Reference) (state : State Symbol Guard) :
    (build (source (body live symbol constraint)) (.reference name :: outer :: captures) state).bind
        (fun value after => work (withoutSelfReference name value) after) =
      work (compileBody (extension (instantiateEdges live captures) symbol constraint outer) name) state := by
  simp only [source_build, body_compile, compileBody, InternedNestedSpecialization.work_bind]

/-- A complete starting cache executes the exact earlier inner request and supplies its canonical record. -/
theorem first_build [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (live : List (EdgeSkeleton Symbol Guard)) (symbol : Symbol) (constraint : Guard)
    (outer : Value Symbol Guard) (captures : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (covered : Covered [] state) :
    build (.binder smart (source (body live symbol constraint))) (outer :: captures) state =
      .done (finish smart (internMu (extension (instantiateEdges live captures) symbol constraint outer) state).1)
        (internMu (extension (instantiateEdges live captures) symbol constraint outer) state).2 := by
  have callbackSame : ∀ name,
      compileBody (instantiate (body live symbol constraint) (outer :: captures)) name =
      compileBody (extension (instantiateEdges live captures) symbol constraint outer) name := by
    intro name
    simp only [compileBody, body_compile]
  have probesSame : probes (instantiate (body live symbol constraint) (outer :: captures)) state =
      probes (extension (instantiateEdges live captures) symbol constraint outer) state := by
    simp only [probes, callbackSame]
  rw [source_binder smart _ _ state coherent covered]
  simp only [internMu, probesSame, finishMu, callbackSame]

/-- A changed enclosing dependency reuses the earlier completed inner binder, even while another Mu is pending. -/
theorem changed_outer [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (live : List (EdgeSkeleton Symbol Guard)) (symbol : Symbol) (constraint : Guard)
    (oldOuter newOuter : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (before after : State Symbol Guard) (coherentBefore : Coherent before) (coherentAfter : Coherent after)
    (growth : Grows (internMu (extension (instantiateEdges live captures) symbol constraint oldOuter) before).2 after) :
    build (.binder smart (source (body live symbol constraint))) (newOuter :: captures) after =
      .done (finish smart (internMu (extension (instantiateEdges live captures) symbol constraint oldOuter) before).1)
        (probes (extension (instantiateEdges live captures) symbol constraint newOuter) after).2 := by
  let template := extension (instantiateEdges live captures) symbol constraint newOuter
  have stored := completed_probe_readback (instantiateEdges live captures) symbol constraint oldOuter newOuter
    before after coherentBefore coherentAfter growth
  have firstCoherent := run_coherent (compileBody template .depth) after
    (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _)) coherentAfter
  have secondCoherent := run_coherent
    (compileBody template (.uninterned (run (compileBody template .depth) after).1.depth))
    (run (compileBody template .depth) after).2
    (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _)) firstCoherent
  obtain ⟨entry, present, _⟩ := secondCoherent.nodes _ _ stored
  simp only [build, body_callback]
  change request smart (probes template after).1.1 (probes template after).1.2
    (fun name state => work (compileBody template name) state) (probes template after).2 = _
  change (probes template after).2.nodes.table (muKey (probes template after).1.1 (probes template after).1.2) = some entry at present
  change (probes template after).2.nodeRecords (muKey (probes template after).1.1 (probes template after).1.2) = _ at stored
  simp only [request, present, stored]
  rfl

end MicroCFTA.InternedNestedErasedEdge
