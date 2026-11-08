import MicroCFTA.SourceSynthesisProgramRoles
import MicroCFTA.SourceSynthesisUniverseConstruction
import MicroCFTA.InternedFreshOrdinarySourceAlignment
import MicroCFTA.InternedShallowValues
import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.EnumerationSoundness

/-!
# Program positions in actual original constructor results

The certificate follows complete stored rows and ordered child values.
Only assigned Type positions permit arbitrary values. A component name can
equal an application or filter name. Its complete guard and layout remain
part of its certificate. Canonical node and union readback retain these
properties. This result does not cover subsequent narrowing or execution.
-/
namespace MicroCFTA.SourceSynthesisProgramBuildRoles
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedEdgeResidency InternedFreshProbeKeys InternedNormalizationFree
open InternedNestedConstruction (Outcome work Syntax EdgeSyntax)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisProgramRoles (ProgramSyntax ProgramRowSyntax)

mutual
/-- Program positions contain only empty, ordinary, or union records. -/
inductive ProgramValue : Value String Guard → Prop where
  | empty : ProgramValue .empty
  | node (entry : Interned NodeKey) (rows : List (EdgeValue String Guard)) (depth : Nat)
      (free : List Reference) (checked : ∀ row ∈ rows, ProgramEdge row) :
      ProgramValue (.node entry rows depth free)
  | union (entry : Interned NodeKey) (members : List (Value String Guard)) (depth : Nat)
      (free : List Reference) (checked : ∀ member ∈ members, ProgramValue member) :
      ProgramValue (.union entry members depth free)

/-- Each complete Program row retains its source guard and assigned child roles. -/
inductive ProgramEdge : EdgeValue String Guard → Prop where
  | annotated (edge : EdgeValue String Guard) (annotation : Value String Guard)
      (guard : edge.entry.key.constraint = top) (children : edge.children = [annotation]) :
      ProgramEdge edge
  | application (edge : EdgeValue String Guard) (types marker function argument : Value String Guard)
      (symbol : edge.entry.key.symbol = "app")
      (guard : edge.entry.key.constraint =
        eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      (children : edge.children = [types, marker, function, argument])
      (functionRole : ProgramValue function) (argumentRole : ProgramValue argument) : ProgramEdge edge
  | filter (edge : EdgeValue String Guard) (goal candidates : Value String Guard)
      (symbol : edge.entry.key.symbol = "filter")
      (guard : edge.entry.key.constraint = eqGuard [[[0], [1, 0]]])
      (children : edge.children = [goal, candidates])
      (candidateRole : ProgramValue candidates) : ProgramEdge edge
end

/-- A Program position cannot be a captured reference. -/
theorem ProgramValue.not_reference (name : Reference) : ¬ ProgramValue (.reference name) := by
  intro role
  cases role

/-- A Program position cannot be a recursive record. -/
theorem ProgramValue.not_mu (entry : Interned NodeKey) (body depth ordinary : Value String Guard) :
    ¬ ProgramValue (.mu entry body depth ordinary) := by
  intro role
  cases role

/-- The actual stored guard has one of the source Program endpoint regions. -/
theorem ProgramEdge.guard_regions (edge : EdgeValue String Guard) (role : ProgramEdge edge) :
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

variable [DecidableEq (EdgeKey String Guard)]

/-- Ordinary normalization retains complete Program rows through pruning and cache hits. -/
theorem makeNode_roles (edges : List (EdgeValue String Guard)) (state : State String Guard)
    (facts : Facts state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (roles : ∀ edge ∈ edges, ProgramEdge edge) : ProgramValue (run (makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedRoles : ∀ edge ∈ canonicalEdges (surviving edges), ProgramEdge edge :=
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

omit [DecidableEq (EdgeKey String Guard)] in
private theorem flatten_roles {value : Value String Guard} (role : ProgramValue value) :
    ∀ member ∈ unionMembers value, ProgramValue member := by
  cases role with
  | empty => simp [unionMembers]
  | node entry rows depth free checked =>
      simpa [unionMembers] using ProgramValue.node entry rows depth free checked
  | union entry members depth free checked => exact checked

omit [DecidableEq (EdgeKey String Guard)] in
private theorem ordinaryEdges_roles (values : List (Value String Guard)) (edges : List (EdgeValue String Guard))
    (roles : ∀ value ∈ values, ProgramValue value) (found : ordinaryEdges values = some edges) :
    ∀ edge ∈ edges, ProgramEdge edge := by
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
            have head : ∀ edge ∈ own, ProgramEdge edge := by
              have checked := roles (.node entry own depth free) List.mem_cons_self
              cases checked
              assumption
            have remaining := ih later (fun value member => roles value (List.mem_cons_of_mem _ member)) tail
            intro edge member
            exact (List.mem_append.mp member).elim (head edge) (remaining edge)

/-- Literal union normalization preserves Program positions in every source branch. -/
theorem makeUnion_roles (values : List (Value String Guard)) (state : State String Guard)
    (facts : Facts state) (available : Values state values) (roles : ∀ value ∈ values, ProgramValue value) :
    ProgramValue (run (makeUnion values) state).1 := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available source (available source included) value present
  have allRoles : ∀ value ∈ distinctNodes (values.flatMap unionMembers), ProgramValue value := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact flatten_roles (roles source included) value present
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa [makeUnion, normalized, run] using ProgramValue.empty
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using allRoles first (by simp [normalized])
      | cons second tail =>
          have inputs : Values state (first :: second :: tail) := by
            intro value member
            exact allAvailable value (by simpa only [normalized] using member)
          have safe : ∀ value ∈ first :: second :: tail, ProgramValue value := by simpa [normalized] using allRoles
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (inputs value member).resident) ordinary
              simpa only [makeUnion, normalized, ordinary] using
                makeNode_roles edges state facts resident (ordinaryEdges_roles _ edges safe ordinary)
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
              have resultRoles : ProgramValue result := by
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

private def Preserves (expression : Expression) : Prop :=
  ∀ (environment : List (Value String Guard)) (before : State String Guard) (value : Value String Guard)
    (after : State String Guard), Facts before → Values before environment →
    InternedFreshOrdinaryConstruction.build expression environment before = .done value after → ProgramValue value

private def EdgePreserves (source : Row) : Prop :=
  ∀ (environment : List (Value String Guard)) (edge : EdgeValue String Guard),
    InternedFreshOrdinarySourceAlignment.EdgeCall environment source edge → ProgramEdge edge

private theorem many_roles (expressions : List Expression) (checked : ∀ expression ∈ expressions, Preserves expression)
    (environment : List (Value String Guard)) (before : State String Guard) (values : List (Value String Guard))
    (after : State String Guard) (facts : Facts before) (inputs : Values before environment)
    (done : InternedFreshOrdinaryConstruction.buildMany expressions environment before = .done values after) :
    ∀ value ∈ values, ProgramValue value := by
  have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls expressions environment before values after facts inputs done
  apply EnumerationSoundness.all₂_outputs ProgramValue expressions values
  apply MergedPhysicalGroupCalls.all₂_left_imp _ _ _ _ aligned
  intro expression member value call
  obtain ⟨start, finish, startFacts, startInputs, called⟩ := call
  exact checked expression member environment start value finish startFacts startInputs called

private theorem edges_roles (expressions : List Row) (checked : ∀ expression ∈ expressions, EdgePreserves expression)
    (environment : List (Value String Guard)) (before : State String Guard) (edges : List (EdgeValue String Guard))
    (after : State String Guard) (facts : Facts before) (inputs : Values before environment)
    (done : InternedFreshOrdinaryConstruction.buildEdges expressions environment before = .done edges after) :
    ∀ edge ∈ edges, ProgramEdge edge := by
  have aligned := InternedFreshOrdinarySourceAlignment.buildEdges_calls expressions environment before edges after facts inputs done
  apply EnumerationSoundness.all₂_outputs ProgramEdge expressions edges
  apply MergedPhysicalGroupCalls.all₂_left_imp _ _ _ _ aligned
  intro expression member edge call
  exact checked expression member environment edge call

private theorem source_preserves {expression : Expression} (role : ProgramSyntax expression) : Preserves expression := by
  induction role using ProgramSyntax.rec (motive_2 := fun row _ => EdgePreserves row) with
  | empty =>
      intro environment before value after _ _ done
      simp only [InternedFreshOrdinaryConstruction.build, Outcome.done.injEq] at done
      obtain ⟨rfl, rfl⟩ := done
      exact .empty
  | node rows _ checked =>
      intro environment before value after facts inputs done
      cases built : InternedFreshOrdinaryConstruction.buildEdges rows environment before with
      | pending key state => simp only [InternedFreshOrdinaryConstruction.build, built, Outcome.bind] at done; cases done
      | done edges middle =>
          have verified := InternedFreshOrdinaryFacts.buildEdges_verified rows environment before facts inputs
          have middleFacts : Facts middle := by simpa only [built, Outcome.state] using verified.facts
          have resident := verified.result edges middle built
          have roles := edges_roles rows checked environment before edges middle facts inputs built
          have result := makeNode_roles edges middle middleFacts resident roles
          have same : run (makeNode edges) middle = (value, after) :=
            Prod.ext (Outcome.done.inj (by
              simpa only [InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).1
              (Outcome.done.inj (by
                simpa only [InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).2
          simpa only [same] using result
  | union members _ checked =>
      intro environment before value after facts inputs done
      cases built : InternedFreshOrdinaryConstruction.buildMany members environment before with
      | pending key state => simp only [InternedFreshOrdinaryConstruction.build, built, Outcome.bind] at done; cases done
      | done values middle =>
          have verified := InternedFreshOrdinaryFacts.buildMany_verified members environment before facts inputs
          have middleFacts : Facts middle := by simpa only [built, Outcome.state] using verified.facts
          have available := verified.result values middle built
          have roles := many_roles members checked environment before values middle facts inputs built
          have result := makeUnion_roles values middle middleFacts available roles
          have same : run (makeUnion values) middle = (value, after) :=
            Prod.ext (Outcome.done.inj (by
              simpa only [InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).1
              (Outcome.done.inj (by
                simpa only [InternedFreshOrdinaryConstruction.build, built, Outcome.bind, work] using done)).2
          simpa only [same] using result
  | annotated name annotation =>
      intro environment edge call
      obtain ⟨start, middle, next, values, facts, inputs, built, made, symbol, guard, children⟩ := call
      have aligned := InternedFreshOrdinarySourceAlignment.buildMany_calls [annotation] environment start values middle facts inputs built
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

/-- An actual completed Program build derives its physical role certificate. -/
theorem build_program (expression : Expression) (role : ProgramSyntax expression)
    (environment : List (Value String Guard)) (before : State String Guard) (value : Value String Guard)
    (after : State String Guard) (facts : Facts before) (inputs : Values before environment)
    (done : InternedFreshOrdinaryConstruction.build expression environment before = .done value after) :
    ProgramValue value := source_preserves role environment before value after facts inputs done

/-- Actual original FirstOrder construction derives physical roles from empty records. -/
theorem firstOrderRaw_build_roles (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (size : Int) (expression : Expression)
    (returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size = .ok expression) :
    ∃ value final, InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ ProgramValue value ∧ Grows empty final ∧
      Cache.Extends (empty (Symbol := String) (Guard := Guard)).nodes.issued final.nodes.issued := by
  obtain ⟨value, final, done, facts, available, growth, history⟩ :=
    SourceSynthesisUniverseConstruction.firstOrderRaw_constructor_complete lib query size expression returned
  exact ⟨value, final, done, facts, available,
    build_program expression (SourceSynthesisProgramRoles.firstOrderRaw_roles lib query size expression returned)
      [] empty value final empty_facts (by intro child member; cases member) done,
    growth, history⟩

/-- Source errors remain explicit; every constructed original result has physical Program roles. -/
theorem firstOrderRaw_build_result (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ value final, InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
          Facts final ∧ Available final value ∧ ProgramValue value ∧ Grows empty final ∧
          Cache.Extends (empty (Symbol := String) (Guard := Guard)).nodes.issued final.nodes.issued := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact firstOrderRaw_build_roles lib query size expression returned

end MicroCFTA.SourceSynthesisProgramBuildRoles
