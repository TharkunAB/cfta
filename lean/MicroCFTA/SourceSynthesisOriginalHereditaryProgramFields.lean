import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceSynthesisOriginalProgramTypeFields

/-!
# Recursive Program fields from original construction

The original syntax assigns every Type and Program operand by position.
Each physical operand retains its actual ordered source call and context.
The completed original build supplies the conditional Mu store at each
earlier call. The proof retains recursive Program facts through source
unions and actual row normalization. It assumes no future classification.
-/
namespace MicroCFTA.SourceSynthesisOriginalHereditaryProgramFields
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize eqGuard)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisInitialTypeFields (Program ProgramRow)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityAnnotationConstruction (Allowed)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "BasicContext" => InternedFreshOrdinaryContext.Context
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "ordinaryChildren" => SourceSynthesisUniverseCallerBoundary.ordinaryChildren
local notation "ordinaryEdges" => SourceSynthesisUniverseCallerBoundary.ordinaryEdges
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable [DecidableEq (EdgeKey Symbol Guard)]

private def Returns (lib : Library) (reader : State Symbol Guard) (expression : Expression) : Prop :=
  ∀ before, BasicContext before [] → ∀ value after,
    build (ordinarySymbols expression) [] before = .done value after → Grows after reader →
      ValueFields (Origin lib) literal value

private def RowReturns (lib : Library) (reader : State Symbol Guard) : Row → Prop
  | .mk symbol guard children =>
      ∀ before, BasicContext before [] → ∀ (values : List (Value Symbol Guard))
        (middle : State Symbol Guard) (edge : EdgeValue Symbol Guard),
        buildMany (ordinaryChildren children) [] before = .done values middle → Grows middle reader →
        edge.entry.key.symbol = literal symbol → edge.entry.key.constraint = guard → edge.children = values →
          EdgeFields (Origin lib) literal edge

private theorem program_slot (lib : Library) (reader : State Symbol Guard) (field : Expression)
    (checked : Returns lib reader field) (expressions : List (Syntax Symbol Guard))
    (before : State Symbol Guard) (context : BasicContext before []) (values : List (Value Symbol Guard))
    (middle : State Symbol Guard) (actual : buildMany expressions [] before = .done values middle)
    (growth : Grows middle reader) (index : Nat) (found : expressions[index]? = some (ordinarySymbols field))
    (value : Value Symbol Guard) (selected : values[index]? = some value) :
    ValueFields (Origin lib) literal value := by
  obtain ⟨chosen, start, finish, lookup, entered, called, _first, last⟩ :=
    SourceSynthesisOriginalProgramTypeFields.many_call expressions before middle reader context values actual
      growth index (ordinarySymbols field) found
  have own := checked start entered chosen finish called last
  have same : chosen = value := Option.some.inj (lookup.symm.trans selected)
  exact same ▸ own

private theorem many_fields (lib : Library) (reader : State Symbol Guard)
    (expressions : List Expression) (checked : ∀ expression ∈ expressions, Returns lib reader expression)
    (before : State Symbol Guard) (context : BasicContext before [])
    (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (actual : buildMany (ordinaryChildren expressions) [] before = .done values after)
    (growth : Grows after reader) : ∀ value ∈ values, ValueFields (Origin lib) literal value := by
  induction expressions generalizing before values with
  | nil =>
      simp only [SourceSynthesisUniverseCallerBoundary.ordinaryChildren, buildMany, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      intro value member; cases member
  | cons first rest ih =>
      cases one : build (ordinarySymbols first) [] before with
      | pending key state =>
          simp only [SourceSynthesisUniverseCallerBoundary.ordinaryChildren, buildMany, one, Outcome.bind] at actual
          cases actual
      | done value middle =>
          cases tail : buildMany (ordinaryChildren rest) [] middle with
          | pending key state =>
              simp only [SourceSynthesisUniverseCallerBoundary.ordinaryChildren, buildMany, one, tail, Outcome.bind] at actual
              cases actual
          | done remaining final =>
              simp only [SourceSynthesisUniverseCallerBoundary.ordinaryChildren, buildMany, one, tail, Outcome.bind,
                Outcome.done.injEq] at actual
              obtain ⟨rfl, rfl⟩ := actual
              have nextContext : BasicContext middle [] := by
                simpa only [one, Outcome.state] using context.build (ordinarySymbols first)
              have verified := InternedFreshOrdinaryFacts.buildMany_verified (ordinaryChildren rest) [] middle
                nextContext.normal.facts nextContext.inputs
              have nextGrowth : Grows middle reader := grows_trans
                (by simpa only [tail, Outcome.state] using verified.growth) growth
              have firstFields := checked first List.mem_cons_self before context value middle one nextGrowth
              have restFields := ih (fun expression member => checked expression (List.mem_cons_of_mem _ member))
                middle nextContext remaining tail
              intro value member
              rcases List.mem_cons.mp member with rfl | member
              · exact firstFields
              · exact restFields value member

private theorem rows_fields (lib : Library) (reader : State Symbol Guard)
    (rows : List Row) (checked : ∀ row ∈ rows, RowReturns lib reader row)
    (before : State Symbol Guard) (context : BasicContext before [])
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : buildEdges (ordinaryEdges rows) [] before = .done edges after)
    (growth : Grows after reader) : ∀ edge ∈ edges, EdgeFields (Origin lib) literal edge := by
  induction rows generalizing before edges with
  | nil =>
      simp only [SourceSynthesisUniverseCallerBoundary.ordinaryEdges, buildEdges, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      intro edge member; cases member
  | cons row rows ih =>
      cases row with
      | mk symbol guard children =>
          cases childDone : buildMany (ordinaryChildren children) [] before with
          | pending key state =>
              simp only [SourceSynthesisUniverseCallerBoundary.ordinaryEdges, buildEdges, childDone, Outcome.bind] at actual
              cases actual
          | done values middle =>
              have middleContext : BasicContext middle [] := by
                simpa only [childDone, Outcome.state] using context.many (ordinaryChildren children)
              have childChecked := InternedFreshOrdinaryFacts.buildMany_verified (ordinaryChildren children) [] before
                context.normal.facts context.inputs
              have inputs := childChecked.result values middle childDone
              let made := run (makeEdge (literal symbol) guard values) middle
              have madeChecked := InternedNestedFacts.edge_verified (literal symbol) guard values middle
                middleContext.normal.facts inputs
              have nextContext : BasicContext made.2 [] := middleContext.edge (literal symbol) guard values inputs
              cases tail : buildEdges (ordinaryEdges rows) [] made.2 with
              | pending key state =>
                  simp only [SourceSynthesisUniverseCallerBoundary.ordinaryEdges, buildEdges, childDone, Outcome.bind, work] at actual
                  change (buildEdges (ordinaryEdges rows) [] made.2).bind
                    (fun rest final => .done (made.1 :: rest) final) = .done edges after at actual
                  simp only [tail, Outcome.bind] at actual
                  cases actual
              | done remaining final =>
                  simp only [SourceSynthesisUniverseCallerBoundary.ordinaryEdges, buildEdges, childDone, Outcome.bind, work] at actual
                  change (buildEdges (ordinaryEdges rows) [] made.2).bind
                    (fun rest final => .done (made.1 :: rest) final) = .done edges after at actual
                  simp only [tail, Outcome.bind, Outcome.done.injEq] at actual
                  obtain ⟨rfl, rfl⟩ := actual
                  have tailChecked := InternedFreshOrdinaryFacts.buildEdges_verified (ordinaryEdges rows) [] made.2
                    nextContext.normal.facts nextContext.inputs
                  have nextGrowth : Grows made.2 reader := grows_trans
                    (by simpa only [tail, Outcome.state] using tailChecked.growth) growth
                  have middleGrowth := grows_trans madeChecked.growth nextGrowth
                  have physical := MergedPhysicalGroupEdges.makeEdge_fields middle middleContext.normal.facts
                    (literal symbol) guard values inputs
                  have own := checked (.mk symbol guard children) List.mem_cons_self
                    before context values middle made.1 childDone middleGrowth physical.1 physical.2.1 physical.2.2
                  have later := ih (fun row member => checked row (List.mem_cons_of_mem _ member))
                    made.2 nextContext remaining tail
                  intro edge member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact own
                  · exact later edge member

section Original
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value Symbol Guard) (reader : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue reader)

include accepted built in
private theorem typed_slot (expressions : List (Syntax Symbol Guard)) (before : State Symbol Guard)
    (context : BasicContext before []) (values : List (Value Symbol Guard)) (middle : State Symbol Guard)
    (actual : buildMany expressions [] before = .done values middle) (growth : Grows middle reader)
    (index : Nat) (field : Expression) (found : expressions[index]? = some (ordinarySymbols field))
    (value : Value Symbol Guard) (selected : values[index]? = some value)
    (allowed : Allowed (Origin lib) (ordinarySymbols field)) : Annotated (Origin lib) value := by
  obtain ⟨chosen, start, finish, lookup, entered, called, first, _last⟩ :=
    SourceSynthesisOriginalProgramTypeFields.many_call expressions before middle reader context values actual
      growth index (ordinarySymbols field) found
  have own := SourceSynthesisOriginalTypeAnnotations.build_typed lib query signed whole accepted rootValue reader built
    field start entered first chosen finish called allowed
  have same : chosen = value := Option.some.inj (lookup.symm.trans selected)
  exact same ▸ own

include accepted built in
private theorem annotated_row (name : String) (field : Expression)
    (allowed : Allowed (Origin lib) (ordinarySymbols field)) :
    RowReturns lib reader (.mk name top [field]) := by
  intro before context values middle edge actual growth symbol guard children
  have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls (ordinaryChildren [field]) []
    before values middle context.normal.facts context.inputs actual
  cases aligned with
  | @cons _ annotation _ _ _ tail =>
      cases tail
      exact .annotated edge annotation guard children
        (typed_slot lib query signed whole accepted rootValue reader built _ before context _ middle
          actual growth 0 field rfl annotation rfl allowed)

include accepted built in
/-- Every actual original Program call derives its full recursive field certificate. -/
theorem at_prefix (expression : Expression) (program : Program lib query expression)
    (before : State Symbol Guard) (context : BasicContext before [])
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build (ordinarySymbols expression) [] before = .done value after)
    (growth : Grows after reader) : ValueFields (Origin lib) literal value := by
  have preserves : ∀ expression, Program lib query expression → Returns lib reader expression := by
    intro expression checked
    induction checked using Program.rec (motive_2 := fun row _ => RowReturns lib reader row) with
    | empty =>
        intro _before _context value after actual _growth
        simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build, Outcome.done.injEq] at actual
        obtain ⟨rfl, rfl⟩ := actual
        exact .empty
    | node rows _ checked =>
        intro before context value after actual growth
        cases rowsDone : buildEdges (ordinaryEdges rows) [] before with
        | pending key state =>
            simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build, rowsDone, Outcome.bind] at actual
            cases actual
        | done edges middle =>
            have verified := InternedFreshOrdinaryFacts.buildEdges_verified (ordinaryEdges rows) [] before
              context.normal.facts context.inputs
            have middleFacts := verified.facts
            simp only [rowsDone, Outcome.state] at middleFacts
            have resident := verified.result edges middle rowsDone
            have same : run (makeNode edges) middle = (value, after) := Prod.ext
              (Outcome.done.inj (by simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build,
                rowsDone, Outcome.bind, work] using actual)).1
              (Outcome.done.inj (by simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build,
                rowsDone, Outcome.bind, work] using actual)).2
            have made := InternedNestedFacts.node_verified edges middle middleFacts resident
            have middleGrowth : Grows middle reader := grows_trans
              (by simpa only [work, same, Outcome.state] using made.growth) growth
            have fields := rows_fields lib reader rows checked before context edges middle rowsDone middleGrowth
            simpa only [same] using SourceSynthesisHereditaryProgramFields.makeNode_fields
              (Origin lib) literal edges middle middleFacts resident fields
    | union members _ checked =>
        intro before context value after actual growth
        cases membersDone : buildMany (ordinaryChildren members) [] before with
        | pending key state =>
            simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build, membersDone, Outcome.bind] at actual
            cases actual
        | done values middle =>
            have verified := InternedFreshOrdinaryFacts.buildMany_verified (ordinaryChildren members) [] before
              context.normal.facts context.inputs
            have middleFacts := verified.facts
            simp only [membersDone, Outcome.state] at middleFacts
            have inputs := verified.result values middle membersDone
            have same : run (makeUnion values) middle = (value, after) := Prod.ext
              (Outcome.done.inj (by simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build,
                membersDone, Outcome.bind, work] using actual)).1
              (Outcome.done.inj (by simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build,
                membersDone, Outcome.bind, work] using actual)).2
            have made := InternedNestedFacts.union_verified values middle middleFacts inputs
            have middleGrowth : Grows middle reader := grows_trans
              (by simpa only [work, same, Outcome.state] using made.growth) growth
            have fields := many_fields lib reader members checked before context values middle membersDone middleGrowth
            simpa only [same] using SourceSynthesisHereditaryProgramFields.makeUnion_fields
              (Origin lib) literal values middle middleFacts inputs fields
    | component entry member =>
        apply annotated_row lib query signed whole accepted rootValue reader built
        simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
          SourceSynthesisOriginalTypeAnnotations.generalized_allowed literal lib query entry.2.1
            (List.mem_append_left _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
    | argumentOnly entry member =>
        apply annotated_row lib query signed whole accepted rootValue reader built
        simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
          SourceSynthesisOriginalTypeAnnotations.generalized_allowed literal lib query entry.2
            (List.mem_append_right _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
    | argument entry member =>
        apply annotated_row lib query signed whole accepted rootValue reader built
        simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
          SourceSynthesisOriginalTypeAnnotations.rigid_allowed literal lib entry.2
    | @application function argument row equation _ _ functionIH argumentIH =>
        have same : .mk "app"
            (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
            [typesOf lib query, arrowMarker top, function, argument] = row :=
          (List.cons.inj (Syntax.node.inj equation)).1
        subst row
        intro before context values middle edge actual growth symbol guard children
        have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls
          (ordinaryChildren [typesOf lib query, arrowMarker top, function, argument]) [] before values middle
          context.normal.facts context.inputs actual
        cases aligned with
        | @cons _ types _ _ _ tail =>
          cases tail with
          | @cons _ marker _ _ _ tail =>
            cases tail with
            | @cons _ first _ _ _ tail =>
              cases tail with
              | @cons _ second _ _ _ tail =>
                cases tail
                refine .application edge types marker first second symbol guard children ?_ ?_ ?_ ?_
                · apply typed_slot lib query signed whole accepted rootValue reader built _ before context _ middle
                    actual growth 0 (typesOf lib query) rfl types rfl
                  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
                    SourceSynthesisOriginalTypeAnnotations.universe_allowed literal lib query
                · apply typed_slot lib query signed whole accepted rootValue reader built _ before context _ middle
                    actual growth 1 (arrowMarker top) rfl marker rfl
                  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
                    SourceSynthesisOriginalTypeAnnotations.marker_allowed literal lib
                · exact program_slot lib reader function functionIH _ before context _ middle actual growth 2 rfl first rfl
                · exact program_slot lib reader argument argumentIH _ before context _ middle actual growth 3 rfl second rfl
    | @filter candidates row equation _ candidateIH =>
        have same : .mk "filter" (eqGuard [[[0], [1, 0]]]) [typeNode top query.queryGoal, candidates] = row :=
          (List.cons.inj (Syntax.node.inj equation)).1
        subst row
        intro before context values middle edge actual growth symbol guard children
        have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls
          (ordinaryChildren [typeNode top query.queryGoal, candidates]) [] before values middle
          context.normal.facts context.inputs actual
        cases aligned with
        | @cons _ goal _ _ _ tail =>
          cases tail with
          | @cons _ candidate _ _ _ tail =>
            cases tail
            refine .filter edge goal candidate symbol guard children ?_ ?_
            · apply typed_slot lib query signed whole accepted rootValue reader built _ before context _ middle
                actual growth 0 (typeNode top query.queryGoal) rfl goal rfl
              simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
                SourceSynthesisOriginalTypeAnnotations.rigid_allowed literal lib query.queryGoal
            · exact program_slot lib reader candidates candidateIH _ before context _ middle actual growth 1 rfl candidate rfl
  exact preserves expression program before context value after actual growth
end Original

/-- Accepted original construction derives all recursive Program and Type-field facts. -/
theorem firstOrderRaw_fields
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols expression) [] empty = .done value heap) :
    ValueFields (Origin lib) literal value :=
  at_prefix lib query signed expression accepted value heap built expression
    (SourceSynthesisInitialTypeFields.firstOrderRaw_fields lib query signed expression accepted)
    empty InternedFreshOrdinaryContext.empty_context value heap built (grows_refl heap)

end MicroCFTA.SourceSynthesisOriginalHereditaryProgramFields
