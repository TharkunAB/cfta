import MicroCFTA.SourceSynthesisInitialTypeFields
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles

/-!
# Original synthesis guard alphabet

The alphabet uses original library Types and the fixed Program guards.
Rigid Types and universe bodies add only Top. Symbol mapping retains guards.
The heap invariant covers all records of the original build, including hits.
Conjunction closure can be infinite. It does not derive UniformReserved,
a numeric Frame, or progress.
-/
namespace MicroCFTA.SourceSynthesisOriginalGuardAlphabet
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses generalize)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisInitialTypeFields (Program ProgramRow)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards Derived)

/-- The literal application guard is independent of the library and request size. -/
def applicationGuard : Guard :=
  eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]]

/-- The literal filter guard is independent of the library and request size. -/
def filterGuard : Guard := eqGuard [[[0], [1, 0]]]

/-- Only generalized library Types add guards beyond the three fixed fields. -/
def alphabet (lib : Library) : List Guard :=
  top :: applicationGuard :: filterGuard ::
    (lib.libraryGroups.map (fun entry => eqGuard (equalityClasses entry.2.1)) ++
      lib.libraryArgumentOnly.map (fun entry => eqGuard (equalityClasses entry.2)))

private theorem top_mem (lib : Library) : top ∈ alphabet lib := List.mem_cons_self

private theorem application_mem (lib : Library) : applicationGuard ∈ alphabet lib :=
  List.mem_cons_of_mem _ List.mem_cons_self

private theorem filter_mem (lib : Library) : filterGuard ∈ alphabet lib :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

private def Good (lib : Library) (expression : Expression) : Prop :=
  ∀ guard ∈ guards expression, guard ∈ alphabet lib

private def GoodRow (lib : Library) : Row → Prop
  | .mk _ guard children => guard ∈ alphabet lib ∧ ∀ child ∈ children, Good lib child

private theorem children_good (lib : Library) (children : List Expression)
    (checked : ∀ child ∈ children, Good lib child) :
    ∀ guard ∈ childGuards children, guard ∈ alphabet lib := by
  induction children with
  | nil => intro guard member; cases member
  | cons first rest ih =>
      intro guard member
      rcases List.mem_append.mp member with own | later
      · exact checked first List.mem_cons_self guard own
      · exact ih (fun child included => checked child (List.mem_cons_of_mem _ included)) guard later

private theorem node_good (lib : Library) (rows : List Row)
    (checked : ∀ row ∈ rows, GoodRow lib row) : Good lib (.node rows) := by
  induction rows with
  | nil => intro guard member; cases member
  | cons row rest ih =>
      cases row with
      | mk name own children =>
          have fields := checked _ List.mem_cons_self
          intro guard member
          rcases List.mem_cons.mp member with same | inside
          · subst guard; exact fields.1
          · rcases List.mem_append.mp inside with child | later
            · exact children_good lib children fields.2 guard child
            · exact ih (fun row included => checked row (List.mem_cons_of_mem _ included)) guard later

private theorem type_good (lib : Library) (typ : Ty) : Good lib (typeNode top typ) := by
  intro guard member
  rw [typeNode_guards top typ guard member]
  exact top_mem lib

private theorem types_good (lib : Library) (query : Query) : Good lib (typesOf lib query) := by
  intro guard member
  rw [allTypes_guards top (constructorCatalog lib query) guard member]
  exact top_mem lib

private theorem generalized_good (lib : Library) (query : Query) (typ : Ty)
    (own : eqGuard (equalityClasses typ) ∈ alphabet lib) :
    Good lib (generalize (typesOf lib query) typ) := by
  intro guard member
  rcases SourceSynthesisGeneralizeSyntax.generalize_guards (typesOf lib query) typ guard member with
    same | trivial | inherited
  · subst guard; exact own
  · subst guard; exact top_mem lib
  · exact types_good lib query guard inherited

private theorem component_good (lib : Library) (query : Query) (name : String) (typ : Ty)
    (own : eqGuard (equalityClasses typ) ∈ alphabet lib) :
    GoodRow lib (component (typesOf lib query) name typ) := by
  refine ⟨top_mem lib, ?_⟩
  intro child member
  have same := List.mem_singleton.mp member
  subst child
  exact generalized_good lib query typ own

/-- The initial source certificate derives the complete literal guard inventory. -/
theorem program_guards (lib : Library) (query : Query) (expression : Expression)
    (fields : Program lib query expression) :
    ∀ guard ∈ guards expression, guard ∈ alphabet lib := by
  change Good lib expression
  induction fields using Program.rec
    (motive_2 := fun row _ => GoodRow lib row) with
  | empty => intro guard member; cases member
  | node rows fields ih => exact node_good lib rows ih
  | union members fields ih => exact children_good lib members ih
  | component entry member =>
      apply component_good lib query entry.1 entry.2.1
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_map.mpr ⟨entry, member, rfl⟩))))
  | argumentOnly entry member =>
      apply component_good lib query entry.1 entry.2
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map.mpr ⟨entry, member, rfl⟩))))
  | argument entry member =>
      refine ⟨top_mem lib, ?_⟩
      intro child included
      have same := List.mem_singleton.mp included
      subst child
      exact type_good lib entry.2
  | @application function argument row actual first second firstIH secondIH =>
      have same : .mk "app" applicationGuard
          [typesOf lib query, arrowMarker top, function, argument] = row :=
        (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      refine ⟨application_mem lib, ?_⟩
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact types_good lib query
      · change Good lib (.node [.mk "(->)" top []])
        apply node_good
        intro row included
        have same := List.mem_singleton.mp included
        subst row
        exact ⟨top_mem lib, by intro child absent; cases absent⟩
      · exact firstIH
      · exact secondIH
  | @filter candidates row actual fields ih =>
      have same : .mk "filter" filterGuard [typeNode top query.queryGoal, candidates] = row :=
        (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      refine ⟨filter_mem lib, ?_⟩
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact type_good lib query.queryGoal
      · exact ih

/-- Accepted original requests use only the input guard alphabet at every literal depth. -/
theorem firstOrderRaw_guards (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression) :
    ∀ guard ∈ guards expression, guard ∈ alphabet lib :=
  program_guards lib query expression
    (SourceSynthesisInitialTypeFields.firstOrderRaw_fields lib query signed expression accepted)

mutual
private theorem mapped_inventory {Symbol : Type} (literal : String → Symbol) (expression : Expression) :
    guards (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) = guards expression := by
  cases expression with
  | empty | var => rfl
  | node rows => simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax, guards, mapped_rows literal rows]
  | union members =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax, guards, mapped_children literal members]
  | binder smart body =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax, guards, mapped_inventory literal body]
termination_by sizeOf expression

private theorem mapped_children {Symbol : Type} (literal : String → Symbol) (expressions : List Expression) :
    childGuards (SourceSynthesisProgramBuildRolesGeneric.mapChildren literal expressions) = childGuards expressions := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapChildren, childGuards,
        mapped_inventory literal first, mapped_children literal rest]
termination_by sizeOf expressions

private theorem mapped_rows {Symbol : Type} (literal : String → Symbol) (rows : List Row) :
    edgeGuards (SourceSynthesisProgramBuildRolesGeneric.mapEdges literal rows) = edgeGuards rows := by
  cases rows with
  | nil => rfl
  | cons row rest =>
      cases row with
      | mk name guard children =>
          simp only [SourceSynthesisProgramBuildRolesGeneric.mapEdges, edgeGuards,
            mapped_children literal children, mapped_rows literal rest]
termination_by sizeOf rows
end

/-- Literal symbol mapping retains the same original guard alphabet. -/
theorem mapped_guards {Symbol : Type} (literal : String → Symbol)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression) :
    ∀ guard ∈ guards (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression),
      guard ∈ alphabet lib := by
  rw [mapped_inventory]
  exact firstOrderRaw_guards lib query signed expression accepted

/-- Every stored record of the actual mapped build has an input-derived guard. -/
theorem constructed {Symbol : Type} (literal : String → Symbol)
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) [] empty = .done value heap) :
    SourceEqualityAnnotationHeap.Heap
      (Derived (alphabet lib) top SourceEqualityPCSNativeEdge.conjoin) heap := by
  have allowed := SourceEqualityConstraintOrigins.allowed
    (Derived (alphabet lib) top SourceEqualityPCSNativeEdge.conjoin)
    (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression)
    (fun guard member => Derived.literal (mapped_guards literal lib query signed expression accepted guard member))
  simpa only [built, Outcome.state] using SourceEqualityAnnotationConstruction.build
    (Derived (alphabet lib) top SourceEqualityPCSNativeEdge.conjoin)
    (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) allowed [] empty
    (SourceEqualityAnnotationHeap.empty_heap _)

/-- The existing caller's Label construction retains the same complete heap invariant. -/
theorem label_constructed (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value (SourceObservations.Label FullSyntax.Formula) Guard)
    (heap : State (SourceObservations.Label FullSyntax.Formula) Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap) :
    SourceEqualityAnnotationHeap.Heap
      (Derived (alphabet lib) top SourceEqualityPCSNativeEdge.conjoin) heap := by
  apply constructed SourceSynthesisLabelProgramBuildRoles.literal lib query signed expression accepted value heap
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built

/-- Accepted input data derives an actual mapped build and its whole-record invariant. -/
theorem complete {Symbol : Type} (literal : String → Symbol)
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression) :
    ∃ value heap,
      InternedFreshOrdinaryConstruction.build
        (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) [] empty = .done value heap ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet lib) top SourceEqualityPCSNativeEdge.conjoin) heap := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete
    (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression)
  exact ⟨value, heap, built, constructed literal lib query signed expression accepted value heap built⟩

end MicroCFTA.SourceSynthesisOriginalGuardAlphabet
