import MicroCFTA.SourceSynthesisInitialTypeFields
import MicroCFTA.SourceSynthesisOriginalTypeAnnotations
import MicroCFTA.SourceSynthesisAnnotationFieldConstructors
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles

/-!
# Original Program heads retain their constructed Type fields

The source certificate assigns the first child of every Program row.
Actual ordered calls derive its Type annotation at the same resident value.
The completed call heap grows into the original completed construction.
This derives each earlier Mu store without a supplied annotation invariant.
Node and union normalization retain the resulting first-field certificate.
These laws describe original construction. They do not prove preservation
through subsequent Program edits or assign Type origins to Program guards.
-/
namespace MicroCFTA.SourceSynthesisOriginalProgramTypeFields
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize eqGuard)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisInitialTypeFields (Program ProgramRow)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityAnnotationConstruction (Allowed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "BasicContext" => InternedFreshOrdinaryContext.Context
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "ordinaryChildren" => SourceSynthesisUniverseCallerBoundary.ordinaryChildren
local notation "ordinaryEdges" => SourceSynthesisUniverseCallerBoundary.ordinaryEdges
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Each ordered child retains its actual source call and both prefix growth facts. -/
theorem many_call (expressions : List (Syntax Symbol Guard))
    (before after reader : State Symbol Guard) (context : BasicContext before [])
    (values : List (Value Symbol Guard)) (actual : buildMany expressions [] before = .done values after)
    (growth : Grows after reader) (index : Nat) (expression : Syntax Symbol Guard)
    (found : expressions[index]? = some expression) :
    ∃ value start finish, values[index]? = some value ∧ BasicContext start [] ∧
      build expression [] start = .done value finish ∧ Grows start reader ∧ Grows finish reader := by
  induction expressions generalizing before values index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      cases one : build first [] before with
      | pending key state => simp only [buildMany, one, Outcome.bind] at actual; cases actual
      | done value middle =>
          cases tail : buildMany rest [] middle with
          | pending key state => simp only [buildMany, one, tail, Outcome.bind] at actual; cases actual
          | done remaining final =>
              simp only [buildMany, one, tail, Outcome.bind, Outcome.done.injEq] at actual
              obtain ⟨rfl, rfl⟩ := actual
              have nextContext : BasicContext middle [] := by
                simpa only [one, Outcome.state] using context.build first
              have tailChecked := InternedFreshOrdinaryFacts.buildMany_verified rest [] middle
                nextContext.normal.facts nextContext.inputs
              have tailGrowth : Grows middle final := by
                simpa only [tail, Outcome.state] using tailChecked.growth
              have nextGrowth := grows_trans tailGrowth growth
              cases index with
              | zero =>
                  have field : first = expression := Option.some.inj found
                  subst expression
                  have checked := InternedFreshOrdinaryFacts.build_verified first [] before
                    context.normal.facts context.inputs
                  have firstGrowth : Grows before middle := by
                    simpa only [one, Outcome.state] using checked.growth
                  exact ⟨value, before, middle, rfl, context, one,
                    grows_trans firstGrowth nextGrowth, nextGrowth⟩
              | succ index =>
                  obtain ⟨chosen, start, finish, selected, entered, called, initial, last⟩ :=
                    ih middle nextContext remaining tail index found
                  exact ⟨chosen, start, finish, selected, entered, called, initial, last⟩

private def HeadAllowed (lib : Library) : Row → Prop
  | .mk _ _ children => ∃ field rest, children = field :: rest ∧
      Allowed (Origin lib) (ordinarySymbols field)

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem row_head (lib : Library) (query : Query) {row : Row}
    (program : ProgramRow lib query row) : HeadAllowed lib row := by
  cases program with
  | component entry member =>
      refine ⟨generalize (typesOf lib query) entry.2.1, [], rfl, ?_⟩
      simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
        SourceSynthesisOriginalTypeAnnotations.generalized_allowed
          SourceSynthesisLabelProgramBuildRoles.literal lib query entry.2.1
          (List.mem_append_left _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
  | argumentOnly entry member =>
      refine ⟨generalize (typesOf lib query) entry.2, [], rfl, ?_⟩
      simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
        SourceSynthesisOriginalTypeAnnotations.generalized_allowed
          SourceSynthesisLabelProgramBuildRoles.literal lib query entry.2
          (List.mem_append_right _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
  | argument entry _ =>
      refine ⟨typeNode top entry.2, [], rfl, ?_⟩
      simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
        SourceSynthesisOriginalTypeAnnotations.rigid_allowed
          SourceSynthesisLabelProgramBuildRoles.literal lib entry.2
  | @application function argument row actual _ _ =>
      have same : .mk "app"
          (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
          [typesOf lib query, arrowMarker top, function, argument] = row :=
        (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      refine ⟨typesOf lib query, _, rfl, ?_⟩
      simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
        SourceSynthesisOriginalTypeAnnotations.universe_allowed
          SourceSynthesisLabelProgramBuildRoles.literal lib query
  | @filter candidates row actual _ =>
      have same : .mk "filter" (eqGuard [[[0], [1, 0]]])
          [typeNode top query.queryGoal, candidates] = row :=
        (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      refine ⟨typeNode top query.queryGoal, _, rfl, ?_⟩
      simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
        SourceSynthesisOriginalTypeAnnotations.rigid_allowed
          SourceSynthesisLabelProgramBuildRoles.literal lib query.queryGoal

private def Returns (lib : Library) (reader : State Symbol Guard) (expression : Expression) : Prop :=
  ∀ before, BasicContext before [] → ∀ value after,
    build (ordinarySymbols expression) [] before = .done value after → Grows after reader →
      AnnotationFields (Origin lib) value

private theorem many_fields (lib : Library) (reader : State Symbol Guard)
    (expressions : List Expression) (checked : ∀ expression ∈ expressions, Returns lib reader expression)
    (before : State Symbol Guard) (context : BasicContext before [])
    (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (actual : buildMany (ordinaryChildren expressions) [] before = .done values after)
    (growth : Grows after reader) : ∀ value ∈ values, AnnotationFields (Origin lib) value := by
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
              simp only [SourceSynthesisUniverseCallerBoundary.ordinaryChildren, buildMany, one, tail, Outcome.bind, Outcome.done.injEq] at actual
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

private theorem edges_fields
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (reader : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue reader)
    (rows : List Row) (heads : ∀ row ∈ rows, HeadAllowed lib row)
    (before : State Symbol Guard) (context : BasicContext before [])
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : buildEdges (ordinaryEdges rows) [] before = .done edges after)
    (growth : Grows after reader) :
    ∀ edge ∈ edges, ∀ value, edge.children[0]? = some value → Annotated (Origin lib) value := by
  induction rows generalizing before edges with
  | nil =>
      simp only [SourceSynthesisUniverseCallerBoundary.ordinaryEdges, buildEdges, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      intro edge member; cases member
  | cons row rows ih =>
      cases row with
      | mk symbol guard children =>
          obtain ⟨field, rest, rfl, allowed⟩ := heads _ List.mem_cons_self
          cases childDone : buildMany (ordinaryChildren (field :: rest)) [] before with
          | pending key state =>
              simp only [SourceSynthesisUniverseCallerBoundary.ordinaryEdges, buildEdges, childDone, Outcome.bind] at actual
              cases actual
          | done values middle =>
              have middleContext : BasicContext middle [] := by
                simpa only [childDone, Outcome.state] using context.many (ordinaryChildren (field :: rest))
              have childChecked := InternedFreshOrdinaryFacts.buildMany_verified (ordinaryChildren (field :: rest)) [] before
                context.normal.facts context.inputs
              have inputs := childChecked.result values middle childDone
              let made := run (makeEdge (symbol, .top) guard values) middle
              have madeChecked := InternedNestedFacts.edge_verified (symbol, .top) guard values middle
                middleContext.normal.facts inputs
              have nextContext : BasicContext made.2 [] := middleContext.edge (symbol, .top) guard values inputs
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
                  obtain ⟨chosen, start, finish, selected, startContext, called, startGrowth, _⟩ :=
                    many_call (ordinaryChildren (field :: rest)) before middle reader context values childDone
                      middleGrowth 0 (ordinarySymbols field) rfl
                  have typed := SourceSynthesisOriginalTypeAnnotations.build_typed lib query signed whole accepted
                    rootValue reader built field start startContext startGrowth chosen finish called allowed
                  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleContext.normal.facts
                    (symbol, .top) guard values inputs
                  have later := ih (fun row member => heads row (List.mem_cons_of_mem _ member))
                    made.2 nextContext remaining tail
                  intro edge member value found
                  rcases List.mem_cons.mp member with rfl | member
                  · have lookup : values[0]? = some value := by
                      change (run (makeEdge (symbol, .top) guard values) middle).1.children[0]? = some value at found
                      simpa only [fields.2.2] using found
                    have same : chosen = value := Option.some.inj (selected.symm.trans lookup)
                    exact same ▸ typed
                  · exact later edge member value found

/-- An actual original Program call derives its own annotated first fields. -/
theorem at_prefix
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (reader : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue reader)
    (expression : Expression) (program : Program lib query expression)
    (before : State Symbol Guard) (context : BasicContext before [])
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build (ordinarySymbols expression) [] before = .done value after)
    (growth : Grows after reader) : AnnotationFields (Origin lib) value := by
  have preserves : ∀ expression, Program lib query expression → Returns lib reader expression := by
    intro expression checked
    induction checked using Program.rec (motive_2 := fun _ _ => True) with
    | empty =>
        intro _before _context value after actual _growth
        simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build, Outcome.done.injEq] at actual
        obtain ⟨rfl, rfl⟩ := actual
        exact .empty
    | node rows sourceRows _ =>
        intro before context value after actual growth
        cases rowsDone : buildEdges (ordinaryEdges rows) [] before with
        | pending key state =>
            simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build, rowsDone, Outcome.bind] at actual
            cases actual
        | done edges middle =>
            have checked := InternedFreshOrdinaryFacts.buildEdges_verified (ordinaryEdges rows) [] before
              context.normal.facts context.inputs
            have middleFacts := checked.facts
            simp only [rowsDone, Outcome.state] at middleFacts
            have resident := checked.result edges middle rowsDone
            have same : run (makeNode edges) middle = (value, after) := Prod.ext
              (Outcome.done.inj (by simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build,
                rowsDone, Outcome.bind, work] using actual)).1
              (Outcome.done.inj (by simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build,
                rowsDone, Outcome.bind, work] using actual)).2
            have made := InternedNestedFacts.node_verified edges middle middleFacts resident
            have middleGrowth : Grows middle reader := grows_trans
              (by simpa only [work, same, Outcome.state] using made.growth) growth
            have fields := edges_fields lib query signed whole accepted rootValue reader built rows
              (fun row member => row_head lib query (sourceRows row member)) before context edges middle rowsDone middleGrowth
            have result := SourceSynthesisAnnotationFieldConstructors.makeNode_fields
              (Origin lib) edges middle middleFacts resident fields
            simpa only [same] using result
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
            have result := SourceSynthesisAnnotationFieldConstructors.makeUnion_fields
              (Origin lib) values middle middleFacts inputs fields
            simpa only [same] using result
    | component | argumentOnly | argument | application | filter => trivial
  exact preserves expression program before context value after actual growth

/-- Accepted original construction supplies the Program certificate and all prefix facts. -/
theorem firstOrderRaw_fields
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols expression) [] empty = .done value heap) :
    AnnotationFields (Origin lib) value :=
  at_prefix lib query signed expression accepted value heap built expression
    (SourceSynthesisInitialTypeFields.firstOrderRaw_fields lib query signed expression accepted)
    empty InternedFreshOrdinaryContext.empty_context value heap built (grows_refl heap)

end MicroCFTA.SourceSynthesisOriginalProgramTypeFields
