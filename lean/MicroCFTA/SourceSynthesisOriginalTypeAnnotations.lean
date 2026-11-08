import MicroCFTA.SourceSynthesisOriginalPrefixMuStore
import MicroCFTA.SourceSynthesisNativeTypeTrace

/-!
# Annotations of actual original Type-field calls

Original Type instructions use only the Type guard pool. Captured calls use
their actual source contexts and prefix growth. Source paths derive the
literal-reference environments. Original completed construction supplies
the earlier conditional Mu store. No output annotation or store is assumed.
These are initial seed laws, not generated Type grammar or progress laws.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeAnnotations
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses generalize)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisNativeTypeTrace (Origin pool origin_top)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityAnnotationConstruction (Allowed ManyAllowed EdgesAllowed)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

/-- Only the actual generalized library entries add non-Top Type fields. -/
def OriginalType (lib : Library) (typ : Ty) : Prop :=
  typ ∈ lib.libraryGroups.map (fun entry => entry.2.1) ++ lib.libraryArgumentOnly.map Prod.snd

private theorem generalized_origin (lib : Library) (typ : Ty) (original : OriginalType lib typ) :
    Origin lib (eqGuard (equalityClasses typ)) := by
  apply SourceEqualityConstraintOrigins.Derived.literal
  rcases List.mem_append.mp original with group | argument
  · obtain ⟨entry, included, rfl⟩ := List.mem_map.mp group
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨entry, included, rfl⟩))
  · obtain ⟨entry, included, rfl⟩ := List.mem_map.mp argument
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨entry, included, rfl⟩))

mutual
private theorem map_allowed {S : Type} (literal : String → S) (valid : Guard → Prop)
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
      exact map_allowed literal valid body allowed
termination_by sizeOf expression

private theorem map_children_allowed {S : Type} (literal : String → S) (valid : Guard → Prop)
    (expressions : List Expression) (allowed : ManyAllowed valid expressions) :
    ManyAllowed valid (mapChildren literal expressions) := by
  cases expressions with
  | nil => simp only [mapChildren, ManyAllowed]
  | cons first rest =>
      simp only [mapChildren, ManyAllowed] at allowed ⊢
      exact ⟨map_allowed literal valid first allowed.1, map_children_allowed literal valid rest allowed.2⟩
termination_by sizeOf expressions

private theorem map_rows_allowed {S : Type} (literal : String → S) (valid : Guard → Prop)
    (rows : List Row) (allowed : EdgesAllowed valid rows) : EdgesAllowed valid (mapEdges literal rows) := by
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

/-- Actual generalized library Types satisfy the pool predicate after any literal symbol map. -/
theorem generalized_allowed {S : Type} (literal : String → S) (lib : Library) (query : Query)
    (typ : Ty) (original : OriginalType lib typ) :
    Allowed (Origin lib) (mapSyntax literal (generalize (typesOf lib query) typ)) := by
  apply map_allowed
  apply SourceEqualityConstraintOrigins.allowed
  intro guard member
  rcases SourceSynthesisGeneralizeSyntax.generalize_guards (typesOf lib query) typ guard member with
    own | trivial | inherited
  · subst guard; exact generalized_origin lib typ original
  · subst guard; exact origin_top lib
  · rw [allTypes_guards top (constructorCatalog lib query) guard inherited]
    exact origin_top lib

/-- Every rigid original Type instruction has only Top fields. -/
theorem rigid_allowed {S : Type} (literal : String → S) (lib : Library) (typ : Ty) :
    Allowed (Origin lib) (mapSyntax literal (typeNode top typ)) := by
  apply map_allowed
  apply SourceEqualityConstraintOrigins.allowed
  intro guard member
  rw [typeNode_guards top typ guard member]
  exact origin_top lib

/-- The actual shared universe instruction has only Top fields, including binder bodies. -/
theorem universe_allowed {S : Type} (literal : String → S) (lib : Library) (query : Query) :
    Allowed (Origin lib) (mapSyntax literal (typesOf lib query)) := by
  apply map_allowed
  apply SourceEqualityConstraintOrigins.allowed
  intro guard member
  rw [allTypes_guards top (constructorCatalog lib query) guard member]
  exact origin_top lib

/-- The application marker is an ordinary Top leaf. -/
theorem marker_allowed {S : Type} (literal : String → S) (lib : Library) :
    Allowed (Origin lib) (mapSyntax literal (arrowMarker top)) := by
  apply map_allowed
  apply SourceEqualityConstraintOrigins.allowed
  intro guard member
  have same := List.mem_singleton.mp member
  subst guard
  exact origin_top lib

private theorem at_prefix [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (finalHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) [] empty = .done rootValue finalHeap)
    (field : Expression) (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before environment) (growth : Grows before finalHeap)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field) environment before = .done result after)
    (allowed : Allowed (Origin lib) (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field))
    (annotations : ∀ value ∈ environment, Annotated (Origin lib) value) : Annotated (Origin lib) result := by
  have stored := SourceSynthesisOriginalPrefixMuStore.prefix_muStored (Origin lib) (origin_top lib)
    lib query signed whole accepted rootValue finalHeap built before growth
  have checked := SourceCurrentHereditaryConstruction.build (Origin lib)
    (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field) environment before context.normal.facts
    context.inputs allowed annotations stored
  exact checked.result result after actual

/-- A literal original Program field call derives its Type annotation from actual construction. -/
theorem build_typed [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (finalHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) [] empty = .done rootValue finalHeap)
    (field : Expression) (before : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before []) (growth : Grows before finalHeap)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field) [] before = .done result after)
    (allowed : Allowed (Origin lib) (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field)) :
    Annotated (Origin lib) result :=
  at_prefix lib query signed whole accepted rootValue finalHeap built field [] before context growth
    result after actual allowed (by intro value member; cases member)

/-- Actual crossed binders derive the annotated environment of a captured original Type call. -/
theorem captured_build_typed [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (finalHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) [] empty = .done rootValue finalHeap)
    (field : Expression) (environment : List (Value Symbol Guard))
    (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
    (path : InternedFreshOrdinaryActiveOrigins.Path
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) []
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field) environment crossings)
    (before : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context before environment)
    (growth : Grows before finalHeap) (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field) environment before = .done result after)
    (allowed : Allowed (Origin lib) (SourceSynthesisUniverseCallerBoundary.ordinarySymbols field)) :
    Annotated (Origin lib) result := by
  have references : environment = crossings.map (fun crossing => Value.reference crossing.name) := by
    simpa only [List.append_nil] using path.inputs
  apply at_prefix lib query signed whole accepted rootValue finalHeap built field environment before context growth
    result after actual allowed
  intro value member
  rw [references] at member
  obtain ⟨crossing, _included, rfl⟩ := List.mem_map.mp member
  exact Annotated.reference crossing.name

end MicroCFTA.SourceSynthesisOriginalTypeAnnotations
