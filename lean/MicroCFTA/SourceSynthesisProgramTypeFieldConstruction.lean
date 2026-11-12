import MicroCFTA.SourceSynthesisCurrentTypeOperands
import MicroCFTA.SourceSynthesisHereditaryProgramFields

/-!
# Type fields through the same actual Program build

The source roles select Program operands. The ordered operand list selects
complete Type instructions. Actual predecessor calls carry the current Mu
store to the next call. The returned physical value retains every Type field.
-/
namespace MicroCFTA.SourceSynthesisProgramTypeFieldConstruction
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisTypeSyntax (Library Query arrowMarker)
open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisProgramRoles (ProgramSyntax)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
open SourceSynthesisCurrentTypeOperands (typeOperands rowTypeOperands)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceEqualityAnnotationConstruction (Allowed)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
variable {S : Type} [DecidableEq (EdgeKey S Guard)]
local notation "Context" => InternedFreshOrdinaryContext.Context

private def Step (literal : String → S) (valid : Guard → Prop)
    (expression : Expression) (post : Value S Guard → Prop) : Prop :=
  ∀ before, Context before [] → MuStored valid before → ∀ value after,
    build (mapSyntax literal expression) [] before = .done value after →
      MuStored valid after ∧ post value

private def RowStep (literal : String → S) (valid : Guard → Prop) : Row → Prop
  | .mk symbol guard children =>
      ∀ before, Context before [] → MuStored valid before →
        ∀ (values : List (Value S Guard)) middle (edge : EdgeValue S Guard),
          buildMany (mapChildren literal children) [] before = .done values middle →
          edge.entry.key.symbol = literal symbol → edge.entry.key.constraint = guard →
          edge.children = values → MuStored valid middle ∧ EdgeFields valid literal edge

private theorem type_step (literal : String → S) (valid : Guard → Prop)
    (expression : Expression) (allowed : Allowed valid (mapSyntax literal expression)) :
    Step literal valid expression (Annotated valid) := by
  intro before context stored value after actual
  have checked := SourceCurrentHereditaryConstruction.build valid (mapSyntax literal expression)
    [] before context.normal.facts context.inputs allowed (by intro value member; cases member) stored
  exact ⟨by simpa only [actual, Outcome.state] using checked.stored,
    checked.result value after actual⟩

private theorem many_post (literal : String → S) (valid : Guard → Prop)
    (expressions : List Expression) (posts : List (Value S Guard → Prop))
    (steps : All₂ (Step literal valid) expressions posts)
    (before : State S Guard) (context : Context before []) (stored : MuStored valid before)
    (values : List (Value S Guard)) (after : State S Guard)
    (actual : buildMany (mapChildren literal expressions) [] before = .done values after) :
    MuStored valid after ∧ All₂ (fun post value => post value) posts values := by
  induction steps generalizing before values after with
  | nil =>
      simp only [mapChildren, buildMany, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      exact ⟨stored, .nil⟩
  | @cons first post rest posts firstStep _ ih =>
      cases one : build (mapSyntax literal first) [] before with
      | pending key state =>
          simp only [mapChildren, buildMany, one, Outcome.bind] at actual
          cases actual
      | done value middle =>
          cases tail : buildMany (mapChildren literal rest) [] middle with
          | pending key state =>
              simp only [mapChildren, buildMany, one, tail, Outcome.bind] at actual
              cases actual
          | done remaining final =>
              simp only [mapChildren, buildMany, one, tail, Outcome.bind, Outcome.done.injEq] at actual
              obtain ⟨rfl, rfl⟩ := actual
              have nextContext : Context middle [] := by
                simpa only [one, Outcome.state] using context.build (mapSyntax literal first)
              obtain ⟨nextStored, firstPost⟩ := firstStep before context stored value middle one
              obtain ⟨lastStored, later⟩ := ih middle nextContext nextStored remaining final tail
              exact ⟨lastStored, .cons firstPost later⟩

private theorem many_uniform (literal : String → S) (valid : Guard → Prop)
    (expressions : List Expression) (post : Value S Guard → Prop)
    (checked : ∀ expression ∈ expressions, Step literal valid expression post)
    (before : State S Guard) (context : Context before []) (stored : MuStored valid before)
    (values : List (Value S Guard)) (after : State S Guard)
    (actual : buildMany (mapChildren literal expressions) [] before = .done values after) :
    MuStored valid after ∧ ∀ value ∈ values, post value := by
  have steps : All₂ (Step literal valid) expressions (expressions.map (fun _ => post)) := by
    clear actual
    induction expressions with
    | nil => exact .nil
    | cons first rest ih =>
        exact .cons (checked first List.mem_cons_self)
          (ih (fun expression member => checked expression (List.mem_cons_of_mem _ member)))
  obtain ⟨kept, related⟩ := many_post literal valid expressions _ steps before context stored values after actual
  have uniform := (SymbolicGraphView.all₂_map_iff (fun (p : Value S Guard → Prop) value => p value)
    (fun (_ : Expression) => post) expressions values).mp related
  exact ⟨kept, EnumerationSoundness.all₂_outputs post expressions values uniform⟩

private theorem rows_fields (literal : String → S) (valid : Guard → Prop)
    (rows : List Row) (checked : ∀ row ∈ rows, RowStep literal valid row)
    (before : State S Guard) (context : Context before []) (stored : MuStored valid before)
    (edges : List (EdgeValue S Guard)) (after : State S Guard)
    (actual : buildEdges (mapEdges literal rows) [] before = .done edges after) :
    MuStored valid after ∧ ∀ edge ∈ edges, EdgeFields valid literal edge := by
  induction rows generalizing before edges with
  | nil =>
      simp only [mapEdges, buildEdges, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      exact ⟨stored, by intro edge member; cases member⟩
  | cons row rows ih =>
      cases row with
      | mk symbol guard children =>
          cases childDone : buildMany (mapChildren literal children) [] before with
          | pending key state =>
              simp only [mapEdges, buildEdges, childDone, Outcome.bind] at actual
              cases actual
          | done values middle =>
              have middleContext : Context middle [] := by
                simpa only [childDone, Outcome.state] using context.many (mapChildren literal children)
              have verified := InternedFreshOrdinaryFacts.buildMany_verified (mapChildren literal children)
                [] before context.normal.facts context.inputs
              have inputs := verified.result values middle childDone
              let made := run (makeEdge (literal symbol) guard values) middle
              have nextContext : Context made.2 [] := middleContext.edge (literal symbol) guard values inputs
              cases tail : buildEdges (mapEdges literal rows) [] made.2 with
              | pending key state =>
                  simp only [mapEdges, buildEdges, childDone, Outcome.bind, work] at actual
                  change (buildEdges (mapEdges literal rows) [] made.2).bind
                    (fun rest final => .done (made.1 :: rest) final) = .done edges after at actual
                  simp only [tail, Outcome.bind] at actual
                  cases actual
              | done remaining final =>
                  simp only [mapEdges, buildEdges, childDone, Outcome.bind, work] at actual
                  change (buildEdges (mapEdges literal rows) [] made.2).bind
                    (fun rest final => .done (made.1 :: rest) final) = .done edges after at actual
                  simp only [tail, Outcome.bind, Outcome.done.injEq] at actual
                  obtain ⟨rfl, rfl⟩ := actual
                  have physical := MergedPhysicalGroupEdges.makeEdge_fields middle middleContext.normal.facts
                    (literal symbol) guard values inputs
                  obtain ⟨middleStored, own⟩ := checked (.mk symbol guard children) List.mem_cons_self
                    before context stored values middle made.1 childDone physical.1 physical.2.1 physical.2.2
                  have nextStored : MuStored valid made.2 := middleStored.makeEdge (literal symbol) guard values
                  obtain ⟨kept, later⟩ := ih
                    (fun row member => checked row (List.mem_cons_of_mem _ member))
                    made.2 nextContext nextStored remaining tail
                  refine ⟨kept, ?_⟩
                  intro edge member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact own
                  · exact later edge member

private theorem source_fields (literal : String → S) (valid : Guard → Prop)
    (expression : Expression) (roles : ProgramSyntax expression) :
    (∀ field ∈ typeOperands expression, Allowed valid (mapSyntax literal field)) →
      Step literal valid expression (ValueFields valid literal) := by
  induction roles using ProgramSyntax.rec
    (motive_2 := fun row _ =>
      (∀ field ∈ rowTypeOperands row, Allowed valid (mapSyntax literal field)) →
        RowStep literal valid row) with
  | empty =>
      intro _operands _before _context stored value after actual
      simp only [mapSyntax, build, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      exact ⟨stored, .empty⟩
  | node rows _ checked =>
      intro operands before context stored value after actual
      cases rowsDone : buildEdges (mapEdges literal rows) [] before with
      | pending key state =>
          simp only [mapSyntax, build, rowsDone, Outcome.bind] at actual
          cases actual
      | done edges middle =>
          have verified := InternedFreshOrdinaryFacts.buildEdges_verified (mapEdges literal rows) [] before
            context.normal.facts context.inputs
          have middleFacts := verified.facts
          simp only [rowsDone, Outcome.state] at middleFacts
          have resident := verified.result edges middle rowsDone
          have same : run (makeNode edges) middle = (value, after) := Prod.ext
            (Outcome.done.inj (by simpa only [mapSyntax, build, rowsDone, Outcome.bind, work] using actual)).1
            (Outcome.done.inj (by simpa only [mapSyntax, build, rowsDone, Outcome.bind, work] using actual)).2
          obtain ⟨middleStored, fields⟩ := rows_fields literal valid rows (by
            intro row member
            apply checked row member
            intro field inside
            apply operands
            rw [typeOperands]
            exact List.mem_flatMap.mpr ⟨row, member, inside⟩)
            before context stored edges middle rowsDone
          have result := And.intro (middleStored.makeNode edges)
            (SourceSynthesisHereditaryProgramFields.makeNode_fields valid literal edges middle
              middleFacts resident fields)
          simpa only [same] using result
  | union members _ checked =>
      intro operands before context stored value after actual
      cases membersDone : buildMany (mapChildren literal members) [] before with
      | pending key state =>
          simp only [mapSyntax, build, membersDone, Outcome.bind] at actual
          cases actual
      | done values middle =>
          have verified := InternedFreshOrdinaryFacts.buildMany_verified (mapChildren literal members) [] before
            context.normal.facts context.inputs
          have middleFacts := verified.facts
          simp only [membersDone, Outcome.state] at middleFacts
          have inputs := verified.result values middle membersDone
          have same : run (makeUnion values) middle = (value, after) := Prod.ext
            (Outcome.done.inj (by simpa only [mapSyntax, build, membersDone, Outcome.bind, work] using actual)).1
            (Outcome.done.inj (by simpa only [mapSyntax, build, membersDone, Outcome.bind, work] using actual)).2
          obtain ⟨middleStored, fields⟩ := many_uniform literal valid members (ValueFields valid literal) (by
            intro member included
            apply checked member included
            intro field inside
            apply operands
            rw [typeOperands]
            exact List.mem_flatMap.mpr ⟨member, included, inside⟩)
            before context stored values middle membersDone
          have result := And.intro (middleStored.makeUnion values)
            (SourceSynthesisHereditaryProgramFields.makeUnion_fields valid literal values middle
              middleFacts inputs fields)
          simpa only [same] using result
  | annotated name annotation =>
      rename_i operands
      intro before context stored values middle edge actual _symbol guard children
      have allowed := operands annotation (by simp [rowTypeOperands])
      have steps : All₂ (Step literal valid) [annotation] [Annotated valid] :=
        .cons (type_step literal valid annotation allowed) .nil
      obtain ⟨kept, aligned⟩ := many_post literal valid [annotation] _ steps
        before context stored values middle actual
      cases aligned with
      | cons typed tail =>
          cases tail
          exact ⟨kept, .annotated edge _ guard children typed⟩
  | @application types function argument row equation _ _ functionIH argumentIH =>
      have same := (List.cons.inj (Syntax.node.inj equation)).1
      subst row
      rename_i operands
      intro before context stored values middle edge actual symbol guard children
      have typesAllowed := operands types (by simp [rowTypeOperands])
      have markerAllowed := operands (arrowMarker top) (by simp [rowTypeOperands])
      have firstOperands : ∀ field ∈ typeOperands function, Allowed valid (mapSyntax literal field) := by
        intro field inside
        apply operands
        simp only [rowTypeOperands, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (Or.inl inside))
      have secondOperands : ∀ field ∈ typeOperands argument, Allowed valid (mapSyntax literal field) := by
        intro field inside
        apply operands
        simp only [rowTypeOperands, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (Or.inr inside))
      have steps : All₂ (Step literal valid) [types, arrowMarker top, function, argument]
          [Annotated valid, Annotated valid, ValueFields valid literal, ValueFields valid literal] :=
        .cons (type_step literal valid types typesAllowed)
          (.cons (type_step literal valid (arrowMarker top) markerAllowed)
            (.cons (functionIH firstOperands) (.cons (argumentIH secondOperands) .nil)))
      obtain ⟨kept, aligned⟩ := many_post literal valid _ _ steps before context stored values middle actual
      cases aligned with
      | cons typesTyped tail =>
          cases tail with
          | cons markerTyped tail =>
              cases tail with
              | cons functionFields tail =>
                  cases tail with
                  | cons argumentFields tail =>
                      cases tail
                      exact ⟨kept, .application edge _ _ _ _ symbol guard children
                        typesTyped markerTyped functionFields argumentFields⟩
  | @filter candidates goal row equation _ candidateIH =>
      have same := (List.cons.inj (Syntax.node.inj equation)).1
      subst row
      rename_i operands
      intro before context stored values middle edge actual symbol guard children
      have goalAllowed := operands goal (by simp [rowTypeOperands])
      have candidateOperands : ∀ field ∈ typeOperands candidates, Allowed valid (mapSyntax literal field) := by
        intro field inside
        apply operands
        simp only [rowTypeOperands, List.mem_cons]
        exact Or.inr inside
      have steps : All₂ (Step literal valid) [goal, candidates]
          [Annotated valid, ValueFields valid literal] :=
        .cons (type_step literal valid goal goalAllowed) (.cons (candidateIH candidateOperands) .nil)
      obtain ⟨kept, aligned⟩ := many_post literal valid _ _ steps before context stored values middle actual
      cases aligned with
      | cons goalTyped tail =>
          cases tail with
          | cons candidateFields tail =>
              cases tail
              exact ⟨kept, .filter edge _ _ symbol guard children goalTyped candidateFields⟩

/-- The same successful build retains its Mu store and all physical Program Type fields. -/
theorem build_program_fields (literal : String → S) (valid : Guard → Prop)
    (expression : Expression) (roles : ProgramSyntax expression)
    (operands : ∀ field ∈ typeOperands expression, Allowed valid (mapSyntax literal field))
    (before : State S Guard) (context : Context before []) (stored : MuStored valid before)
    (value : Value S Guard) (after : State S Guard)
    (actual : build (mapSyntax literal expression) [] before = .done value after) :
    MuStored valid after ∧ ValueFields valid literal value :=
  source_fields literal valid expression roles operands before context stored value after actual

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

omit [DecidableEq (EdgeKey S Guard)] in
/-- Actual current root construction derives every physical Type field from its original inputs. -/
theorem current_root_fields [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) [] empty = .done value heap) :
    MuStored (SourceSynthesisNativeTypeTrace.Origin (SourceSynthesisCurrentSourceGuards.encodedLibrary lib)) heap ∧
      ValueFields (SourceSynthesisNativeTypeTrace.Origin (SourceSynthesisCurrentSourceGuards.encodedLibrary lib))
        SourceSynthesisLabelProgramBuildRoles.literal value := by
  obtain ⟨roles, operands⟩ := SourceSynthesisCurrentTypeOperands.current_root_type_operands
    lib query signed whole returned
  apply build_program_fields SourceSynthesisLabelProgramBuildRoles.literal
    (SourceSynthesisNativeTypeTrace.Origin (SourceSynthesisCurrentSourceGuards.encodedLibrary lib)) whole roles
  · simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using operands
  · exact InternedFreshOrdinaryContext.empty_context
  · exact MuStored.empty _
  · simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built

end MicroCFTA.SourceSynthesisProgramTypeFieldConstruction
