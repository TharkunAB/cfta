import MicroCFTA.InternedProbeProvenance

/-!
# Generated template and two-probe provenance

The compiler derives complete record residency and reference reservations
from its actual captured inputs. Source self-union normalization runs
before each probe, as in the constructor implementation.
-/
namespace MicroCFTA.InternedTemplateProvenance
open Cache InternedConstructorTemplates InternedRecordCoherence InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeRef NodeKey)
open InternedProbeProvenance

mutual
/-- The finite captured records occur directly in the original constructor syntax. -/
def captures : Template Symbol Guard → List (Value Symbol Guard)
  | .argument => []
  | .captured value => [value]
  | .node edges => edgeCaptures edges
  | .union members => manyCaptures members
termination_by template => sizeOf template

/-- Ordered source children contribute their own original captured inputs. -/
def manyCaptures : List (Template Symbol Guard) → List (Value Symbol Guard)
  | [] => []
  | first :: rest => captures first ++ manyCaptures rest
termination_by templates => sizeOf templates

/-- Each source edge contributes the captured records of its complete child list. -/
def edgeCaptures : List (EdgeTemplate Symbol Guard) → List (Value Symbol Guard)
  | [] => []
  | .mk _ _ children :: rest => manyCaptures children ++ edgeCaptures rest
termination_by edges => sizeOf edges
end

mutual
/-- Actual template compilation derives the complete output record's provenance. -/
theorem compile_available [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (argument : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (argumentAvailable : Available state argument)
    (captured : ∀ value ∈ captures template, Available state value) :
    Coherent (run (compile template argument) state).2 ∧ Cached (run (compile template argument) state).2 ∧
      Available (run (compile template argument) state).2 (run (compile template argument) state).1 := by
  cases template with
  | argument => simpa only [compile, run] using And.intro coherent (And.intro cached argumentAvailable)
  | captured value =>
      simp only [captures] at captured
      simpa only [compile, run] using And.intro coherent (And.intro cached (captured value List.mem_cons_self))
  | node edges =>
      simp only [captures] at captured
      have built := compileEdges_available edges argument state coherent cached argumentAvailable captured
      simpa only [compile, run_bind] using
        makeNode_available (run (compileEdges edges argument) state).1 _ built.1 built.2.1 built.2.2
  | union members =>
      simp only [captures] at captured
      have built := compileMany_available members argument state coherent cached argumentAvailable captured
      simpa only [compile, run_bind] using
        makeUnion_available (run (compileMany members argument) state).1 _ built.1 built.2.1 built.2.2
termination_by sizeOf template

/-- Each completed child remains available after all later child effects. -/
theorem compileMany_available [DecidableEq (EdgeKey Symbol Guard)] (templates : List (Template Symbol Guard))
    (argument : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (argumentAvailable : Available state argument)
    (captured : ∀ value ∈ manyCaptures templates, Available state value) :
    Coherent (run (compileMany templates argument) state).2 ∧ Cached (run (compileMany templates argument) state).2 ∧
      ∀ value ∈ (run (compileMany templates argument) state).1,
        Available (run (compileMany templates argument) state).2 value := by
  cases templates with
  | nil => simpa only [compileMany, run] using And.intro coherent (And.intro cached (by simp : ∀ value ∈ ([] : List (Value Symbol Guard)), Available state value))
  | cons first rest =>
      simp only [manyCaptures] at captured
      have head := compile_available first argument state coherent cached argumentAvailable
        (fun value member => captured value (List.mem_append_left _ member))
      have tail := compileMany_available rest argument _ head.1 head.2.1
        (available_after_run (compile first argument) state coherent.valid argumentAvailable)
        (fun value member => available_after_run (compile first argument) state coherent.valid
          (captured value (List.mem_append_right _ member)))
      simp only [compileMany, run_bind, InternedConstructorTemplates.run]
      refine ⟨tail.1, tail.2.1, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact available_after_run (compileMany rest argument) _ head.1.valid head.2.2
      · exact tail.2.2 value member
termination_by sizeOf templates

/-- Separate edge interning retains its child inputs and every later edge's completed children. -/
theorem compileEdges_available [DecidableEq (EdgeKey Symbol Guard)] (templates : List (EdgeTemplate Symbol Guard))
    (argument : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (argumentAvailable : Available state argument)
    (captured : ∀ value ∈ edgeCaptures templates, Available state value) :
    Coherent (run (compileEdges templates argument) state).2 ∧ Cached (run (compileEdges templates argument) state).2 ∧
      ∀ child ∈ (run (compileEdges templates argument) state).1.flatMap EdgeValue.children,
        Available (run (compileEdges templates argument) state).2 child := by
  cases templates with
  | nil => simpa only [compileEdges, run, List.flatMap_nil] using And.intro coherent (And.intro cached (by simp : ∀ value ∈ ([] : List (Value Symbol Guard)), Available state value))
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [edgeCaptures] at captured
          have nodes := compileMany_available children argument state coherent cached argumentAvailable
            (fun value member => captured value (List.mem_append_left _ member))
          let built := run (compileMany children argument) state
          have edge := makeEdge_available symbol constraint built.1 built.2 nodes.1 nodes.2.1 nodes.2.2
          let edged := run (makeEdge symbol constraint built.1) built.2
          have argumentAfter : Available edged.2 argument :=
            available_after_run (makeEdge symbol constraint built.1) built.2 nodes.1.valid
              (available_after_run (compileMany children argument) state coherent.valid argumentAvailable)
          have tail := compileEdges_available rest argument edged.2 edge.1 edge.2.1 argumentAfter
            (fun value member => available_after_run (makeEdge symbol constraint built.1) built.2 nodes.1.valid
              (available_after_run (compileMany children argument) state coherent.valid
                (captured value (List.mem_append_right _ member))))
          simp only [compileEdges, run_bind, InternedConstructorTemplates.run]
          refine ⟨tail.1, tail.2.1, ?_⟩
          intro child member
          rcases List.mem_append.mp member with head | member
          · exact available_after_run (compileEdges rest argument) edged.2 edge.1.valid (edge.2.2 child head)
          · exact tail.2.2 child member
termination_by sizeOf templates
end

/-- Removing the bare self operand preserves every retained record and reference reservation. -/
theorem withoutSelfReference_available [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (value : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (available : Available state value) :
    Coherent (run (withoutSelfReference name value) state).2 ∧
      Cached (run (withoutSelfReference name value) state).2 ∧
      Available (run (withoutSelfReference name value) state).2 (run (withoutSelfReference name value) state).1 := by
  cases value <;> simp only [withoutSelfReference]
  all_goals first
    | exact ⟨coherent, cached, available⟩
    | (split
       · exact makeUnion_available _ state coherent cached
           (fun child member => available.children child (List.mem_filter.mp member).1)
       · exact ⟨coherent, cached, available⟩)

/-- The normalized body output derives residency and provenance from actual source inputs. -/
theorem compileBody_available [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (name : Reference) (state : InternedConstructorTemplates.State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state)
    (issued : IssuedReferences (Symbol := Symbol) (Guard := Guard) state.nodes (.reference name))
    (captured : ∀ value ∈ captures template, Available state value) :
    Coherent (run (compileBody template name) state).2 ∧ Cached (run (compileBody template name) state).2 ∧
      Available (run (compileBody template name) state).2 (run (compileBody template name) state).1 := by
  have built := compile_available template (.reference name) state coherent cached
    (reference_available state name issued) captured
  simpa only [compileBody, run_bind] using
    withoutSelfReference_available name (run (compile template (.reference name)) state).1 _ built.1 built.2.1 built.2.2

/-- Both complete source probes derive their residency and prior-reference provenance. -/
theorem probes_available [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (captured : ∀ value ∈ captures template, Available state value) :
    Coherent (probes template state).2 ∧ Cached (probes template state).2 ∧
      Available (probes template state).2 (probes template state).1.1 ∧
      Available (probes template state).2 (probes template state).1.2 := by
  have first := compileBody_available template .depth state coherent cached
    (sentinel_references_issued state.nodes 0).1 captured
  let depth := run (compileBody template .depth) state
  have second := compileBody_available template (.uninterned depth.1.depth) depth.2 first.1 first.2.1
    (sentinel_references_issued depth.2.nodes depth.1.depth).2
    (fun value member => available_after_run (compileBody template .depth) state coherent.valid (captured value member))
  exact ⟨second.1, second.2.1,
    available_after_run (compileBody template (.uninterned depth.1.depth)) depth.2 first.1.valid first.2.2,
    second.2.2⟩

end MicroCFTA.InternedTemplateProvenance
