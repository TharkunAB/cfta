import MicroCFTA.SourceCurrentBuildStructuralRowOrigins

/-!
# Indexed children of actual source row calls

The selected physical child retains its original source position and its
exact ordered build interval. The source prefix supplies the joint context,
physical growth, and issued-name growth. No open-value premise is needed.
-/
namespace MicroCFTA.SourceCurrentIndexedRowCallChildren
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuRetainedAlignment (RowCall)

private theorem member_call [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (context : Context before inputs)
    (values : List (Value Symbol Guard)) (actual : buildMany expressions inputs before = .done values after)
    (index : Nat) (value : Value Symbol Guard) (found : values[index]? = some value) :
    ∃ expression current next,
      expressions[index]? = some expression ∧
      buildMany (expressions.take index) inputs before = .done (values.take index) current ∧
      Context current inputs ∧ build expression inputs current = .done value next ∧
      buildMany (expressions.drop (index + 1)) inputs next = .done (values.drop (index + 1)) after := by
  induction expressions generalizing before values index with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      simp only [List.getElem?_nil] at found
      cases found
  | cons expression expressions ih =>
      cases one : build expression inputs before with
      | pending key state => simp only [buildMany,one,Outcome.bind] at actual; cases actual
      | done first middle =>
        cases tail : buildMany expressions inputs middle with
        | pending key state => simp only [buildMany,one,tail,Outcome.bind] at actual; cases actual
        | done rest final =>
          simp only [buildMany,one,tail,Outcome.bind,Outcome.done.injEq] at actual
          obtain ⟨rfl,rfl⟩ := actual
          cases index with
          | zero =>
              have same : first = value := Option.some.inj found
              subst value
              exact ⟨expression,before,middle,rfl,(by simp only [List.take_zero,buildMany]),context,one,tail⟩
          | succ index =>
              have middleContext : Context middle inputs := by
                simpa only [one,Outcome.state] using context.build expression
              obtain ⟨child,current,next,source,earlier,childContext,called,suffix⟩ :=
                ih middle middleContext rest tail index found
              refine ⟨child,current,next,source,?_,childContext,called,?_⟩
              · simp only [List.take_succ_cons,buildMany,one,Outcome.bind,earlier]
              · simpa only [List.drop_succ_cons,Nat.add_assoc] using suffix

/-- A selected row child retains its exact original source call and strict structural source bound. -/
theorem indexed_child [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (EdgeSyntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (rows : List (EdgeValue Symbol Guard)) (middle after : State Symbol Guard)
    (context : Context before inputs) (sourceIndex : Nat) (symbol : Symbol) (guard : Guard)
    (children : List (Syntax Symbol Guard))
    (call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children)
    (childIndex : Nat) (child : Value Symbol Guard)
    (selected : call.output.children[childIndex]? = some child) :
    ∃ childSyntax current next,
      children[childIndex]? = some childSyntax ∧ call.values[childIndex]? = some child ∧
      buildMany (children.take childIndex) inputs call.current = .done (call.values.take childIndex) current ∧
      Context current inputs ∧ build childSyntax inputs current = .done child next ∧
      buildMany (children.drop (childIndex + 1)) inputs next = .done (call.values.drop (childIndex + 1)) call.middle ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      sizeOf childSyntax < sizeOf (Syntax.node expressions) := by
  have rowContext : Context call.current inputs := by
    simpa only [call.earlier,Outcome.state] using context.edges (expressions.take sourceIndex)
  have valuesSelected : call.values[childIndex]? = some child := by
    rw [← call.children_eq]
    exact selected
  obtain ⟨childSyntax,current,next,syntaxSelected,prefix,childContext,called,suffix⟩ :=
    member_call children inputs call.current call.middle rowContext call.values call.called childIndex child valuesSelected
  have first := InternedFreshOrdinaryFacts.buildEdges_verified (expressions.take sourceIndex) inputs before
    context.base.normal.facts context.base.inputs
  have firstGrowth : Grows before call.current := by
    simpa only [call.earlier,Outcome.state] using first.growth
  have firstIssued : Extends before.nodes.issued call.current.nodes.issued := by
    simpa only [call.earlier,Outcome.state] using first.history
  have second := InternedFreshOrdinaryFacts.buildMany_verified (children.take childIndex) inputs call.current
    rowContext.base.normal.facts rowContext.base.inputs
  have secondGrowth : Grows call.current current := by
    simpa only [prefix,Outcome.state] using second.growth
  have secondIssued : Extends call.current.nodes.issued current.nodes.issued := by
    simpa only [prefix,Outcome.state] using second.history
  have smaller : sizeOf childSyntax < sizeOf (Syntax.node expressions) := by
    have childSmall := List.sizeOf_lt_of_mem (List.mem_of_getElem? syntaxSelected)
    have rowSmall := List.sizeOf_lt_of_mem (List.mem_of_getElem? call.source)
    simp only [Syntax.node.sizeOf_spec,EdgeSyntax.mk.sizeOf_spec] at *
    omega
  exact ⟨childSyntax,current,next,syntaxSelected,valuesSelected,prefix,childContext,called,suffix,
    grows_trans firstGrowth secondGrowth,extends_trans firstIssued secondIssued,smaller⟩

end MicroCFTA.SourceCurrentIndexedRowCallChildren
