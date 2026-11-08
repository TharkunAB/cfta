import MicroCFTA.SourceSynthesisProgramRoles
import MicroCFTA.InternedFreshOrdinarySourceAlignment
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedShallowValues
import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.EnumerationSoundness
import MicroCFTA.SymbolicGraphView

/-!
# Program positions after literal source-symbol mapping

The certificate follows complete stored rows and ordered child values.
Only assigned Type positions permit arbitrary values. A component name can
equal an application or filter name. Its complete guard and layout remain
part of its certificate. Canonical node and union readback retain these
properties. The proof builds the mapped syntax in its own cache. It does not transport
heap identities or establish subsequent execution roles.
-/
namespace MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedEdgeResidency InternedFreshProbeKeys InternedNormalizationFree
open InternedNestedConstruction (Outcome work Syntax EdgeSyntax)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisProgramRoles (ProgramSyntax ProgramRowSyntax)

variable {Symbol : Type}

mutual
/-- Map only symbols. Retain every guard and source instruction. -/
def mapSyntax (literal : String → Symbol) : Syntax String Guard → Syntax Symbol Guard
  | .empty => .empty
  | .var index => .var index
  | .node edges => .node (mapEdges literal edges)
  | .union members => .union (mapChildren literal members)
  | .binder smart body => .binder smart (mapSyntax literal body)

/-- Map ordered child instructions without changing their positions. -/
def mapChildren (literal : String → Symbol) : List (Syntax String Guard) → List (Syntax Symbol Guard)
  | [] => []
  | first :: rest => mapSyntax literal first :: mapChildren literal rest

/-- Map names without changing complete edge guards or child order. -/
def mapEdges (literal : String → Symbol) : List (EdgeSyntax String Guard) → List (EdgeSyntax Symbol Guard)
  | [] => []
  | .mk symbol guard children :: rest =>
      .mk (literal symbol) guard (mapChildren literal children) :: mapEdges literal rest
end

/-- The single-row symbol map agrees with the ordered row-list map. -/
def mapEdge (literal : String → Symbol) : Row → EdgeSyntax Symbol Guard
  | .mk symbol guard children => .mk (literal symbol) guard (mapChildren literal children)

/-- Child mapping is the literal ordered list map. -/
theorem mapChildren_eq_map (literal : String → Symbol) (expressions : List Expression) :
    mapChildren literal expressions = expressions.map (mapSyntax literal) := by
  induction expressions with
  | nil => rfl
  | cons first rest ih => simp only [mapChildren, List.map_cons, ih]

/-- Row mapping is the literal ordered list map. -/
theorem mapEdges_eq_map (literal : String → Symbol) (rows : List Row) :
    mapEdges literal rows = rows.map (mapEdge literal) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases row; simp only [mapEdges, mapEdge, List.map_cons, ih]

mutual
/-- Identity symbol mapping retains the complete original instruction. -/
theorem mapSyntax_id (expression : Expression) : mapSyntax id expression = expression := by
  cases expression with
  | empty | var => rfl
  | node rows => simp only [mapSyntax, mapEdges_id rows]
  | union members => simp only [mapSyntax, mapChildren_id members]
  | binder smart body => simp only [mapSyntax, mapSyntax_id body]
termination_by sizeOf expression

/-- Identity child mapping retains every original position. -/
theorem mapChildren_id (expressions : List Expression) : mapChildren id expressions = expressions := by
  cases expressions with
  | nil => rfl
  | cons first rest => simp only [mapChildren, mapSyntax_id first, mapChildren_id rest]
termination_by sizeOf expressions

/-- Identity row mapping retains complete guards and child lists. -/
theorem mapEdges_id (rows : List Row) : mapEdges id rows = rows := by
  cases rows with
  | nil => rfl
  | cons row rest =>
      cases row with
      | mk symbol guard children => simp only [mapEdges, id_eq, mapChildren_id children, mapEdges_id rest]
termination_by sizeOf rows
end

mutual
/-- Program positions contain only empty, ordinary, or union records. -/
inductive ProgramValue (literal : String → Symbol) : Value Symbol Guard → Prop where
  | empty : ProgramValue literal .empty
  | node (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth : Nat)
      (free : List Reference) (checked : ∀ row ∈ rows, ProgramEdge literal row) :
      ProgramValue literal (.node entry rows depth free)
  | union (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat)
      (free : List Reference) (checked : ∀ member ∈ members, ProgramValue literal member) :
      ProgramValue literal (.union entry members depth free)

/-- Each complete Program row retains its source guard and assigned child roles. -/
inductive ProgramEdge (literal : String → Symbol) : EdgeValue Symbol Guard → Prop where
  | annotated (edge : EdgeValue Symbol Guard) (annotation : Value Symbol Guard)
      (guard : edge.entry.key.constraint = top) (children : edge.children = [annotation]) :
      ProgramEdge literal edge
  | application (edge : EdgeValue Symbol Guard) (types marker function argument : Value Symbol Guard)
      (symbol : edge.entry.key.symbol = literal "app")
      (guard : edge.entry.key.constraint =
        eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      (children : edge.children = [types, marker, function, argument])
      (functionRole : ProgramValue literal function) (argumentRole : ProgramValue literal argument) : ProgramEdge literal edge
  | filter (edge : EdgeValue Symbol Guard) (goal candidates : Value Symbol Guard)
      (symbol : edge.entry.key.symbol = literal "filter")
      (guard : edge.entry.key.constraint = eqGuard [[[0], [1, 0]]])
      (children : edge.children = [goal, candidates])
      (candidateRole : ProgramValue literal candidates) : ProgramEdge literal edge
end

variable (literal : String → Symbol)

/-- A Program position cannot be a captured reference. -/
theorem ProgramValue.not_reference (name : Reference) : ¬ ProgramValue literal (.reference name) := by
  intro role
  cases role

/-- A Program position cannot be a recursive record. -/
theorem ProgramValue.not_mu (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) :
    ¬ ProgramValue literal (.mu entry body depth ordinary) := by
  intro role
  cases role

/-- The actual stored guard has one of the source Program endpoint regions. -/
theorem ProgramEdge.guard_regions (edge : EdgeValue Symbol Guard) (role : ProgramEdge literal edge) :
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
      SourceSynthesisGuardRegions.componentRegion path) ∨
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
      SourceSynthesisGuardRegions.applicationRegion path) ∨
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
      SourceSynthesisGuardRegions.filterRegion path) := by
  cases role with
  | annotated edge annotation guard children =>
      left
      rw [guard]
      intro path member
      have empty : SourceCompactGuards.sourceEqualities (top : Guard) = some [] := rfl
      rw [empty] at member
      simp [EqualityNormalize.members] at member
  | application edge types marker function argument symbol guard children functionRole argumentRole =>
      right; left
      rw [guard]
      exact (SourceSynthesisGuardRegions.application_guard_endpoints .empty .empty .empty
        "app" _ [.empty, SourceSynthesisTypeSyntax.arrowMarker top, .empty, .empty] rfl).2
  | filter edge goal candidates symbol guard children candidateRole =>
      right; right
      rw [guard]
      exact (SourceSynthesisGuardRegions.filter_guard_endpoints .empty .empty
        "filter" _ [.empty, .empty] rfl).2

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Ordinary normalization retains complete Program rows through pruning and cache hits. -/
theorem makeNode_roles (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (roles : ∀ edge ∈ edges, ProgramEdge literal edge) : ProgramValue literal (run (makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedRoles : ∀ edge ∈ canonicalEdges (surviving edges), ProgramEdge literal edge :=
    fun edge member => roles edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa [same] using selected)
    simp only [run, readback, identifyNode]
    exact .node _ _ _ _ (by simpa [same] using selectedRoles)

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem flatten_roles {value : Value Symbol Guard} (role : ProgramValue literal value) :
    ∀ member ∈ unionMembers value, ProgramValue literal member := by
  cases role with
  | empty => simp [unionMembers]
  | node entry rows depth free checked =>
      simpa [unionMembers] using ProgramValue.node (literal := literal) entry rows depth free checked
  | union entry members depth free checked => exact checked

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem ordinaryEdges_roles (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (roles : ∀ value ∈ values, ProgramValue literal value) (found : ordinaryEdges values = some edges) :
    ∀ edge ∈ edges, ProgramEdge literal edge := by
  induction values generalizing edges with
  | nil => cases found; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry own depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : own ++ later = edges := by simpa [tail] using found
            subst edges
            have head : ∀ edge ∈ own, ProgramEdge literal edge := by
              have checked := roles (.node entry own depth free) List.mem_cons_self
              cases checked
              assumption
            have remaining := ih later (fun value member => roles value (List.mem_cons_of_mem _ member)) tail
            intro edge member
            exact (List.mem_append.mp member).elim (head edge) (remaining edge)

/-- Literal union normalization preserves Program positions in every source branch. -/
theorem makeUnion_roles (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values) (roles : ∀ value ∈ values, ProgramValue literal value) :
    ProgramValue literal (run (makeUnion values) state).1 := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available source (available source included) value present
  have allRoles : ∀ value ∈ distinctNodes (values.flatMap unionMembers), ProgramValue literal value := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact flatten_roles literal (roles source included) value present
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa [makeUnion, normalized, run] using ProgramValue.empty (literal := literal)
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using allRoles first (by simp [normalized])
      | cons second tail =>
          have inputs : Values state (first :: second :: tail) := by
            intro value member
            exact allAvailable value (by simpa only [normalized] using member)
          have safe : ∀ value ∈ first :: second :: tail, ProgramValue literal value := by simpa [normalized] using allRoles
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (inputs value member).resident) ordinary
              simpa only [makeUnion, normalized, ordinary] using
                makeNode_roles literal edges state facts resident (ordinaryEdges_roles literal _ edges safe ordinary)
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have built := makeUnion_available values state facts.coherent facts.cached available
              have output : Available after result := by simpa only [makeUnion, normalized, ordinary, run] using built.2.2
              have later : Coherent after := by simpa only [makeUnion, normalized, ordinary, run] using built.1
              have laterInputs : Values after members := by
                intro value member
                simpa only [makeUnion, normalized, ordinary, run] using
                  available_after_run (makeUnion values) state facts.coherent.valid (inputs value member)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state facts.coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have resultRoles : ProgramValue literal result := by
                change NodeFields key actual result at fields
                generalize resultEq : result = value at fields output ⊢
                cases value with
                | empty | reference | node | mu => simp [NodeFields, muKey, key] at fields
                | union entry actualMembers level free =>
                    have same := value_lists_equal after later members actualMembers
                      (fun value member => (laterInputs value member).resident)
                      (fun value member => (output.children value member).resident)
                      (NodeKey.union.inj fields.2.1)
                    exact .union _ _ _ _ (same ▸ safe)
              simpa only [makeUnion, normalized, ordinary, run] using resultRoles

private def Preserves (literal : String → Symbol) (expression : Expression) : Prop :=
  ∀ (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (value : Value Symbol Guard)
    (after : State Symbol Guard), Facts before → Values before environment →
    InternedFreshOrdinaryConstruction.build (mapSyntax literal expression) environment before = .done value after →
      ProgramValue literal value

private def EdgePreserves (literal : String → Symbol) (source : Row) : Prop :=
  ∀ (environment : List (Value Symbol Guard)) (edge : EdgeValue Symbol Guard),
    InternedFreshOrdinarySourceAlignment.EdgeCall environment (mapEdge literal source) edge → ProgramEdge literal edge

private theorem many_roles (expressions : List Expression) (checked : ∀ expression ∈ expressions, Preserves literal expression)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (values : List (Value Symbol Guard))
    (after : State Symbol Guard) (facts : Facts before) (inputs : Values before environment)
    (done : InternedFreshOrdinaryConstruction.buildMany (mapChildren literal expressions) environment before = .done values after) :
    ∀ value ∈ values, ProgramValue literal value := by
  have mapped := InternedFreshOrdinarySourceAlignment.buildMany_calls
    (mapChildren literal expressions) environment before values after facts inputs done
  have aligned := (SymbolicGraphView.all₂_map_iff
    (fun expression value => ∃ start finish, Facts start ∧ Values start environment ∧
      InternedFreshOrdinaryConstruction.build expression environment start = .done value finish)
    (mapSyntax literal) expressions values).mp (by simpa only [mapChildren_eq_map] using mapped)
  apply EnumerationSoundness.all₂_outputs (ProgramValue literal) expressions values
  apply MergedPhysicalGroupCalls.all₂_left_imp _ _ _ _ aligned
  intro expression member value call
  obtain ⟨start, finish, startFacts, startInputs, called⟩ := call
  exact checked expression member environment start value finish startFacts startInputs called

private theorem edges_roles (expressions : List Row) (checked : ∀ expression ∈ expressions, EdgePreserves literal expression)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (edges : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (facts : Facts before) (inputs : Values before environment)
    (done : InternedFreshOrdinaryConstruction.buildEdges (mapEdges literal expressions) environment before = .done edges after) :
    ∀ edge ∈ edges, ProgramEdge literal edge := by
  have mapped := InternedFreshOrdinarySourceAlignment.buildEdges_calls
    (mapEdges literal expressions) environment before edges after facts inputs done
  have aligned := (SymbolicGraphView.all₂_map_iff
    (InternedFreshOrdinarySourceAlignment.EdgeCall environment) (mapEdge literal) expressions edges).mp
      (by simpa only [mapEdges_eq_map] using mapped)
  apply EnumerationSoundness.all₂_outputs (ProgramEdge literal) expressions edges
  apply MergedPhysicalGroupCalls.all₂_left_imp _ _ _ _ aligned
  intro expression member edge call
  exact checked expression member environment edge call

private theorem source_preserves {expression : Expression} (role : ProgramSyntax expression) : Preserves literal expression := by
  induction role using ProgramSyntax.rec (motive_2 := fun row _ => EdgePreserves literal row) with
  | empty =>
      intro environment before value after _ _ done
      simp only [mapSyntax, InternedFreshOrdinaryConstruction.build, Outcome.done.injEq] at done
      obtain ⟨rfl, rfl⟩ := done
      exact .empty
  | node rows _ checked =>
      intro environment before value after facts inputs done
      cases built : InternedFreshOrdinaryConstruction.buildEdges (mapEdges literal rows) environment before with
      | pending key state =>
          simp only [mapSyntax, InternedFreshOrdinaryConstruction.build, built, Outcome.bind] at done
          cases done
      | done edges middle =>
          have verified := InternedFreshOrdinaryFacts.buildEdges_verified (mapEdges literal rows) environment before facts inputs
          have middleFacts : Facts middle := by simpa only [built, Outcome.state] using verified.facts
          have resident := verified.result edges middle built
          have roles := edges_roles literal rows checked environment before edges middle facts inputs built
          have result := makeNode_roles literal edges middle middleFacts resident roles
          have same : run (makeNode edges) middle = (value, after) :=
            Prod.ext (Outcome.done.inj (by
              simpa only [mapSyntax, InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).1
              (Outcome.done.inj (by
                simpa only [mapSyntax, InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).2
          simpa only [same] using result
  | union members _ checked =>
      intro environment before value after facts inputs done
      cases built : InternedFreshOrdinaryConstruction.buildMany (mapChildren literal members) environment before with
      | pending key state =>
          simp only [mapSyntax, InternedFreshOrdinaryConstruction.build, built, Outcome.bind] at done
          cases done
      | done values middle =>
          have verified := InternedFreshOrdinaryFacts.buildMany_verified (mapChildren literal members) environment before facts inputs
          have middleFacts : Facts middle := by simpa only [built, Outcome.state] using verified.facts
          have available := verified.result values middle built
          have roles := many_roles literal members checked environment before values middle facts inputs built
          have result := makeUnion_roles literal values middle middleFacts available roles
          have same : run (makeUnion values) middle = (value, after) :=
            Prod.ext (Outcome.done.inj (by
              simpa only [mapSyntax, InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).1
              (Outcome.done.inj (by
                simpa only [mapSyntax, InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).2
          simpa only [same] using result
  | annotated name annotation =>
      intro environment edge call
      obtain ⟨start, middle, next, values, facts, inputs, built, made, symbol, guard, children⟩ := call
      have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls
        [mapSyntax literal annotation] environment start values middle facts inputs built
      cases aligned with
      | @cons _ annotationValue _ _ _ tail =>
          cases tail
          exact ProgramEdge.annotated edge annotationValue guard children
  | @application types function argument row actual _ _ functionIH argumentIH =>
      have same := (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      intro environment edge call
      obtain ⟨start, middle, next, values, facts, inputs, built, made, symbol, guard, children⟩ := call
      have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls _ environment start values middle facts inputs built
      cases aligned with
      | @cons _ typeValue _ _ _ tail =>
          cases tail with
          | @cons _ markerValue _ _ _ tail =>
              cases tail with
              | @cons _ functionValue _ _ functionCall tail =>
                  cases tail with
                  | @cons _ argumentValue _ _ argumentCall tail =>
                      cases tail
                      obtain ⟨functionStart, functionAfter, functionFacts, functionInputs, functionDone⟩ := functionCall
                      obtain ⟨argumentStart, argumentAfter, argumentFacts, argumentInputs, argumentDone⟩ := argumentCall
                      exact ProgramEdge.application edge typeValue markerValue functionValue argumentValue symbol guard children
                        (functionIH environment functionStart functionValue functionAfter functionFacts functionInputs functionDone)
                        (argumentIH environment argumentStart argumentValue argumentAfter argumentFacts argumentInputs argumentDone)
  | @filter candidates goal row actual _ candidateIH =>
      have same := (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      intro environment edge call
      obtain ⟨start, middle, next, values, facts, inputs, built, made, symbol, guard, children⟩ := call
      have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls _ environment start values middle facts inputs built
      cases aligned with
      | @cons _ goalValue _ _ _ tail =>
          cases tail with
          | @cons _ candidateValue _ _ candidateCall tail =>
              cases tail
              obtain ⟨candidateStart, candidateAfter, candidateFacts, candidateInputs, candidateDone⟩ := candidateCall
              exact ProgramEdge.filter edge goalValue candidateValue symbol guard children
                (candidateIH environment candidateStart candidateValue candidateAfter candidateFacts candidateInputs candidateDone)

/-- A fresh build of mapped source syntax derives physical Program roles directly. -/
theorem build_mapped_program (expression : Expression) (role : ProgramSyntax expression)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (value : Value Symbol Guard)
    (after : State Symbol Guard) (facts : Facts before) (inputs : Values before environment)
    (done : InternedFreshOrdinaryConstruction.build (mapSyntax literal expression) environment before = .done value after) :
    ProgramValue literal value := source_preserves literal role environment before value after facts inputs done

/-- Original signed requests derive completed mapped construction and physical Program roles. -/
theorem firstOrderRaw_build_roles (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (size : Int) (expression : Expression)
    (returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size = .ok expression) :
    ∃ value final, InternedFreshOrdinaryConstruction.build (mapSyntax literal expression) [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ ProgramValue literal value ∧ Grows empty final ∧
      Cache.Extends (empty : State Symbol Guard).nodes.issued final.nodes.issued := by
  obtain ⟨value, final, done⟩ :=
    InternedFreshOrdinaryClosedCompletion.closed_complete (mapSyntax literal expression)
  have verified := InternedFreshOrdinaryFacts.closed_verified (mapSyntax literal expression)
  have roles := build_mapped_program literal expression
    (SourceSynthesisProgramRoles.firstOrderRaw_roles lib query size expression returned)
    [] empty value final empty_facts (by intro child member; cases member) done
  exact ⟨value, final, done,
    by simpa only [done, Outcome.state] using verified.facts,
    verified.result value final done, roles,
    by simpa only [done, Outcome.state] using verified.growth,
    by simpa only [done, Outcome.state] using verified.history⟩

/-- Source errors remain explicit; accepted requests derive their actual mapped results. -/
theorem firstOrderRaw_build_result (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ value final, InternedFreshOrdinaryConstruction.build (mapSyntax literal expression) [] empty = .done value final ∧
          Facts final ∧ Available final value ∧ ProgramValue literal value ∧ Grows empty final ∧
          Cache.Extends (empty : State Symbol Guard).nodes.issued final.nodes.issued := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact firstOrderRaw_build_roles literal lib query size expression returned

end MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
