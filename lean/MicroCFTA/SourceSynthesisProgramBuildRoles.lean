import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
import MicroCFTA.SourceSynthesisUniverseConstruction

/-!
# String specializations of physical Program roles

The role family and constructor proofs use a literal symbol map.
These aliases retain the original String API and qualified constructors.
Original construction derives its role certificate from empty records.
This module does not identify String heaps with mapped-symbol heaps.
-/
namespace MicroCFTA.SourceSynthesisProgramBuildRoles
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisProgramRoles (ProgramSyntax)

/-- The original String family is the literal identity specialization. -/
abbrev ProgramValue : Value String Guard → Prop :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramValue id

/-- The original complete-row family is the literal identity specialization. -/
abbrev ProgramEdge : EdgeValue String Guard → Prop :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramEdge id

/-- Retain the original qualified empty constructor. -/
abbrev ProgramValue.empty : ProgramValue .empty :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramValue.empty

/-- Retain the original qualified ordinary constructor. -/
abbrev ProgramValue.node (entry : Interned NodeKey) (rows : List (EdgeValue String Guard)) (depth : Nat)
    (free : List Reference) (checked : ∀ row ∈ rows, ProgramEdge row) :
    ProgramValue (.node entry rows depth free) :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramValue.node entry rows depth free checked

/-- Retain the original qualified union constructor. -/
abbrev ProgramValue.union (entry : Interned NodeKey) (members : List (Value String Guard)) (depth : Nat)
    (free : List Reference) (checked : ∀ member ∈ members, ProgramValue member) :
    ProgramValue (.union entry members depth free) :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramValue.union entry members depth free checked

/-- Retain the original qualified annotated-row constructor. -/
abbrev ProgramEdge.annotated (edge : EdgeValue String Guard) (annotation : Value String Guard)
    (guard : edge.entry.key.constraint = top) (children : edge.children = [annotation]) : ProgramEdge edge :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramEdge.annotated edge annotation guard children

/-- Retain the original qualified application-row constructor. -/
abbrev ProgramEdge.application (edge : EdgeValue String Guard) (types marker function argument : Value String Guard)
    (symbol : edge.entry.key.symbol = "app")
    (guard : edge.entry.key.constraint =
      eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    (children : edge.children = [types, marker, function, argument])
    (functionRole : ProgramValue function) (argumentRole : ProgramValue argument) : ProgramEdge edge :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramEdge.application edge types marker function argument
    symbol guard children functionRole argumentRole

/-- Retain the original qualified filter-row constructor. -/
abbrev ProgramEdge.filter (edge : EdgeValue String Guard) (goal candidates : Value String Guard)
    (symbol : edge.entry.key.symbol = "filter")
    (guard : edge.entry.key.constraint = eqGuard [[[0], [1, 0]]])
    (children : edge.children = [goal, candidates]) (candidateRole : ProgramValue candidates) : ProgramEdge edge :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramEdge.filter edge goal candidates symbol guard children candidateRole

/-- Retain the original qualified mutual value recursor. -/
abbrev ProgramValue.rec := @SourceSynthesisProgramBuildRolesGeneric.ProgramValue.rec String id

/-- Retain the original qualified mutual row recursor. -/
abbrev ProgramEdge.rec := @SourceSynthesisProgramBuildRolesGeneric.ProgramEdge.rec String id

/-- A Program position cannot be a captured reference. -/
theorem ProgramValue.not_reference (name : Reference) : ¬ ProgramValue (.reference name) :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramValue.not_reference id name

/-- A Program position cannot be a recursive record. -/
theorem ProgramValue.not_mu (entry : Interned NodeKey) (body depth ordinary : Value String Guard) :
    ¬ ProgramValue (.mu entry body depth ordinary) :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramValue.not_mu id entry body depth ordinary

/-- The actual stored guard has one of the source Program endpoint regions. -/
theorem ProgramEdge.guard_regions (edge : EdgeValue String Guard) (role : ProgramEdge edge) :
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
      SourceSynthesisGuardRegions.componentRegion path) ∨
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
      SourceSynthesisGuardRegions.applicationRegion path) ∨
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
      SourceSynthesisGuardRegions.filterRegion path) :=
  SourceSynthesisProgramBuildRolesGeneric.ProgramEdge.guard_regions id edge role

variable [DecidableEq (EdgeKey String Guard)]

/-- Ordinary normalization retains complete Program rows through pruning and cache hits. -/
theorem makeNode_roles (edges : List (EdgeValue String Guard)) (state : State String Guard)
    (facts : Facts state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (roles : ∀ edge ∈ edges, ProgramEdge edge) : ProgramValue (run (makeNode edges) state).1 :=
  SourceSynthesisProgramBuildRolesGeneric.makeNode_roles id edges state facts resident roles

/-- Literal union normalization preserves Program positions in every source branch. -/
theorem makeUnion_roles (values : List (Value String Guard)) (state : State String Guard)
    (facts : Facts state) (available : Values state values) (roles : ∀ value ∈ values, ProgramValue value) :
    ProgramValue (run (makeUnion values) state).1 :=
  SourceSynthesisProgramBuildRolesGeneric.makeUnion_roles id values state facts available roles

/-- An actual completed Program build derives its physical role certificate. -/
theorem build_program (expression : Expression) (role : ProgramSyntax expression)
    (environment : List (Value String Guard)) (before : State String Guard) (value : Value String Guard)
    (after : State String Guard) (facts : Facts before) (inputs : Values before environment)
    (done : InternedFreshOrdinaryConstruction.build expression environment before = .done value after) :
    ProgramValue value :=
  SourceSynthesisProgramBuildRolesGeneric.build_mapped_program id expression role environment before value after
    facts inputs (by simpa only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax_id] using done)

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
