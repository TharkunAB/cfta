import MicroCFTA.SourceSynthesisCurrentSourceGuards
import MicroCFTA.SourceSynthesisOriginalProgramTypeFields
import MicroCFTA.SourceSynthesisOriginalTypeFieldCalls

/-!
# Type operands at actual current source calls

Arbitrary catalogs retain their literal Type guards. Encoded library schemes
derive the one generalized outer guard from the original input entry.
One current completed build supplies the Mu store at its earlier prefixes.
An actual ordered row call attaches the annotated value to its physical slot.
-/
namespace MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses generalize)
open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisPr210TypeReflection (encodeTy)
open SourceSynthesisNativeTypeTrace (Origin origin_top)
open SourceSynthesisOriginalTypeAnnotations (OriginalType)
open SourceEqualityAnnotationConstruction (Allowed ManyAllowed EdgesAllowed)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "BasicContext" => InternedFreshOrdinaryContext.Context
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

mutual
/-- A symbol map retains the guards of every allowed instruction. -/
theorem mapSyntax_allowed {S : Type} (literal : String → S) (valid : Guard → Prop)
    (expression : Expression) (allowed : Allowed valid expression) :
    Allowed valid (mapSyntax literal expression) := by
  cases expression with
  | empty | var => simp only [mapSyntax, Allowed]
  | node rows =>
      simp only [mapSyntax, Allowed] at allowed ⊢
      exact map_rows_allowed literal valid rows allowed
  | union members =>
      simp only [mapSyntax, Allowed] at allowed ⊢
      exact map_children_allowed literal valid members allowed
  | binder smart body =>
      simp only [mapSyntax, Allowed] at allowed ⊢
      exact mapSyntax_allowed literal valid body allowed
termination_by sizeOf expression

private theorem map_children_allowed {S : Type} (literal : String → S) (valid : Guard → Prop)
    (expressions : List Expression) (allowed : ManyAllowed valid expressions) :
    ManyAllowed valid (mapChildren literal expressions) := by
  cases expressions with
  | nil => simp only [mapChildren, ManyAllowed]
  | cons first rest =>
      simp only [mapChildren, ManyAllowed] at allowed ⊢
      exact ⟨mapSyntax_allowed literal valid first allowed.1,
        map_children_allowed literal valid rest allowed.2⟩
termination_by sizeOf expressions

private theorem map_rows_allowed {S : Type} (literal : String → S) (valid : Guard → Prop)
    (rows : List Row) (allowed : EdgesAllowed valid rows) :
    EdgesAllowed valid (mapEdges literal rows) := by
  cases rows with
  | nil => simp only [mapEdges, EdgesAllowed]
  | cons row rest =>
      cases row with
      | mk name guard children =>
          simp only [mapEdges, EdgesAllowed] at allowed ⊢
          exact ⟨allowed.1, map_children_allowed literal valid children allowed.2.1,
            map_rows_allowed literal valid rest allowed.2.2⟩
termination_by sizeOf rows
end

/-- Every universe instruction has only Top guards, for an arbitrary catalog. -/
theorem allTypes_allowed {S : Type} (literal : String → S)
    (valid : Guard → Prop) (validTop : valid top) (catalog : List (String × Nat)) :
    Allowed valid (mapSyntax literal (allTypes top catalog)) := by
  apply mapSyntax_allowed
  apply SourceEqualityConstraintOrigins.allowed
  intro guard member
  rw [allTypes_guards top catalog guard member]
  exact validTop

/-- Generalization adds only its own outer guard to the Top universe. -/
theorem generalize_allTypes_allowed {S : Type} (literal : String → S)
    (valid : Guard → Prop) (validTop : valid top) (catalog : List (String × Nat))
    (scheme : Ty) (own : valid (eqGuard (equalityClasses scheme))) :
    Allowed valid (mapSyntax literal (generalize (allTypes top catalog) scheme)) := by
  apply mapSyntax_allowed
  apply SourceEqualityConstraintOrigins.allowed
  intro guard member
  rcases SourceSynthesisGeneralizeSyntax.generalize_guards (allTypes top catalog) scheme guard member with
    same | trivial | inherited
  · subst guard; exact own
  · subst guard; exact validTop
  · rw [allTypes_guards top catalog guard inherited]
    exact validTop

/-- A raw library entry supplies its encoded generalized Type guard. -/
theorem current_generalized_allowed {S : Type} (literal : String → S)
    (lib : Library) (catalog : List (String × Nat)) (scheme : Ty)
    (original : OriginalType lib scheme) :
    Allowed (Origin (encodedLibrary lib))
      (mapSyntax literal (generalize (allTypes top catalog) (encodeTy scheme))) := by
  apply generalize_allTypes_allowed literal (Origin (encodedLibrary lib))
    (origin_top (encodedLibrary lib)) catalog (encodeTy scheme)
  apply SourceEqualityConstraintOrigins.Derived.literal
  rcases List.mem_append.mp original with group | argument
  · obtain ⟨entry, included, rfl⟩ := List.mem_map.mp group
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr
      ⟨(entry.1, encodeTy entry.2.1, entry.2.2), List.mem_map.mpr ⟨entry, included, rfl⟩, rfl⟩))
  · obtain ⟨entry, included, rfl⟩ := List.mem_map.mp argument
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr
      ⟨(entry.1, encodeTy entry.2), List.mem_map.mpr ⟨entry, included, rfl⟩, rfl⟩))

section Native
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One actual current build supplies the Mu certificate at each earlier heap prefix. -/
theorem prefix_muStored (valid : Guard → Prop) (validTop : valid top)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (finalHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue finalHeap)
    (before : State Symbol Guard) (growth : Grows before finalHeap) :
    SourceCurrentHereditaryConstruction.MuStored valid before := by
  have clean := (SourceSynthesisCurrentSourceGuards.firstOrderRaw_guards_plainMu
    lib query signed whole accepted).2
  have mapped := SourceSynthesisNativeTypeSites.mapped_plainMu
    SourceSynthesisLabelProgramBuildRoles.literal whole clean
  have ordinaryClean : SourceSynthesisRecursiveOrigins.PlainMu top (ordinarySymbols whole) := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using mapped
  have bodies := SourceSynthesisNativeTypeSites.build_mu_bodies top
    (ordinarySymbols whole) ordinaryClean rootValue finalHeap built
  have stored : SourceCurrentHereditaryConstruction.MuStored valid finalHeap := by
    intro key entry body depth ordinary present _ _
    exact SourceCurrentHereditaryUnconstrained.annotated_mono
      (fun (guard : Guard) (same : guard = top) => same.symm ▸ validTop)
      (bodies key entry body depth ordinary present)
  exact SourceSynthesisOriginalPrefixMuStore.muStored_of_grows valid before finalHeap growth stored

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
variable {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
include accepted built

private theorem typed_slot {guard : Guard} {children : List (Syntax Symbol Guard)}
    (call : RowCall expressions [] before outputs after heap rowIndex symbol guard children)
    (index : Nat) (field : Expression) (found : children[index]? = some (ordinarySymbols field))
    (allowed : Allowed (Origin (encodedLibrary lib)) (ordinarySymbols field)) :
    ∃ value, call.output.children[index]? = some value ∧ Available heap value ∧
      value.free = [] ∧ Annotated (Origin (encodedLibrary lib)) value := by
  obtain ⟨value, start, finish, selected, context, actual, first, _last⟩ :=
    SourceSynthesisOriginalProgramTypeFields.many_call children call.current call.middle heap
      call.context call.values call.called call.middle_growth index (ordinarySymbols field) found
  have stored := prefix_muStored (Origin (encodedLibrary lib)) (origin_top (encodedLibrary lib))
    lib query signed whole accepted rootValue heap built start first
  have checked := SourceCurrentHereditaryConstruction.build (Origin (encodedLibrary lib))
    (ordinarySymbols field) [] start context.normal.facts context.inputs allowed
    (by intro value member; cases member) stored
  have annotation := checked.result value finish actual
  have middleContext : BasicContext call.middle [] := by
    simpa only [call.called, Outcome.state] using call.context.many children
  have made := InternedEdgeResidency.makeEdge_linked symbol guard call.values call.middle
    middleContext.normal.facts.coherent middleContext.normal.facts.linked
  have residentNext : InternedEdgeResidency.EdgeResident call.next call.output := by
    simpa only [call.made] using made.2
  have resident := InternedEdgeResidency.edge_grows call.next heap call.next_growth call.output residentNext
  have originalChecked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have finalFacts : InternedNestedFacts.Facts heap := by
    simpa only [built, Outcome.state] using originalChecked.facts
  have selectedOutput : call.output.children[index]? = some value := by
    simpa only [call.children_eq] using selected
  have available := finalFacts.cached.edges call.output.entry.key call.output resident value
    (List.mem_of_getElem? selectedOutput)
  have closed : value.free = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    obtain ⟨input, absent, _⟩ := InternedFreshOrdinarySourceFreeNames.build_free_origins
      (ordinarySymbols field) [] start context.normal context.inputs context.freeNames context.profiles
      value finish actual name member
    cases absent
  exact ⟨value, selectedOutput, available, closed, annotation⟩

/-- A current component or argument-only call retains its exact closed Type operand. -/
theorem component_call (scheme : Ty) (original : OriginalType lib scheme)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol top
      [ordinarySymbols (generalize
        (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)) (encodeTy scheme))]) :
    ∃ value, call.output.children[0]? = some value ∧ Available heap value ∧
      value.free = [] ∧ Annotated (Origin (encodedLibrary lib)) value := by
  apply typed_slot lib query signed whole accepted rootValue heap built call 0 _ rfl
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    current_generalized_allowed SourceSynthesisLabelProgramBuildRoles.literal lib
      (SourceSynthesisCurrentContext.constructorCatalog lib query) scheme original

end Source
end Native
end MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
