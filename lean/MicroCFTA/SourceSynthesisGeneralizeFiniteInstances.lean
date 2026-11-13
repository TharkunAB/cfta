import MicroCFTA.SourceSynthesisTypeUniverseMembership
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceEqualityPCSConstructors

/-!
# Finite instances of actual generalized source schemes

Substitution keys are encoded variable-leaf symbols. Recognized nullary
constructor leaves use the same keys as source variables. Fun has the
arrow shape only at arity two. Substitution images are finite terms and
must belong to the supplied universe at each demanded key.

These laws do not supply an original program or a typing derivation.
-/
namespace MicroCFTA.SourceSynthesisGeneralizeFiniteInstances
open Language InternedConstructorTemplates
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private def arrow (argument result : Term Symbol) : Term Symbol :=
  .node (literal "->") [.node (literal "(->)") [], argument, result]

/-- Replace each recognized original leaf once, using its encoded symbol. -/
def instantiate (substitution : String → Term Symbol) : Ty → Term Symbol
  | .tVar name => substitution (variableSymbol name)
  | .tFun argument result => arrow (instantiate substitution argument) (instantiate substitution result)
  | .tCons name [] => if isVariableSymbol name then substitution name else .node (literal name) []
  | .tCons name [argument, result] =>
      if name = "Fun" then arrow (instantiate substitution argument) (instantiate substitution result)
      else .node (literal name) [instantiate substitution argument, instantiate substitution result]
  | .tCons name arguments => .node (literal name) (arguments.map (instantiate substitution))

/-- A substituted arrow retains its marker and ordered endpoint instances. -/
theorem instantiate_fun (substitution : String → Term Symbol) (argument result : Ty) :
    instantiate substitution (.tFun argument result) =
      .node (literal "->") [.node (literal "(->)") [],
        instantiate substitution argument, instantiate substitution result] := by
  simp only [instantiate, arrow]

private theorem shift_member (index : Nat) (items : List (String × List Nat)) (name : String) (path : List Nat) :
    (name, path) ∈ shift index items ↔ ∃ rest, path = index :: rest ∧ (name, rest) ∈ items := by
  simp only [shift, List.mem_map]
  constructor
  · rintro ⟨⟨symbol, rest⟩, member, same⟩
    cases same
    exact ⟨rest, rfl, member⟩
  · rintro ⟨rest, rfl, member⟩
    exact ⟨(name, rest), member, rfl⟩

private theorem children_origin (index : Nat) (types : List Ty) :
    ∀ name path, (name, path) ∈ childrenOccurrences index types →
      ∃ offset typ rest, types[offset]? = some typ ∧ path = (index + offset) :: rest ∧
        (name, rest) ∈ occurrences typ := by
  induction types generalizing index with
  | nil =>
      intro name path member
      simp only [childrenOccurrences, List.not_mem_nil] at member
  | cons first rest ih =>
      intro name path member
      rw [childrenOccurrences] at member
      rcases List.mem_append.mp member with own | later
      · obtain ⟨tail, same, found⟩ := (shift_member index _ name path).mp own
        exact ⟨0, first, tail, rfl, by simpa only [Nat.add_zero] using same, found⟩
      · obtain ⟨offset, typ, tail, atIndex, same, found⟩ := ih (index + 1) name path later
        refine ⟨offset + 1, typ, tail, ?_, ?_, found⟩
        · simpa only [List.getElem?_cons_succ] using atIndex
        · have equal : index + 1 + offset = index + (offset + 1) := by omega
          simpa only [equal] using same

private theorem child_member (index : Nat) (types : List Ty) (typ : Ty) (included : typ ∈ types)
    (name : String) (path : List Nat) (found : (name, path) ∈ occurrences typ) :
    ∃ actual, (name, actual) ∈ childrenOccurrences index types := by
  induction types generalizing index with
  | nil => cases included
  | cons first rest ih =>
      simp only [childrenOccurrences]
      rcases List.mem_cons.mp included with rfl | later
      · exact ⟨index :: path, List.mem_append.mpr (Or.inl
          ((shift_member index _ name _).mpr ⟨path, rfl, found⟩))⟩
      · obtain ⟨actual, member⟩ := ih (index + 1) later
        exact ⟨actual, List.mem_append.mpr (Or.inr member)⟩

private def OccurrencePaths (substitution : String → Term Symbol) (typ : Ty) : Prop :=
  ∀ name path, (name, path) ∈ occurrences typ →
    (instantiate substitution typ).atPath path = some (substitution name)

private theorem node_paths (substitution : String → Term Symbol) (symbol : Symbol)
    (front : List (Term Symbol)) (types : List Ty)
    (checked : ∀ typ ∈ types, OccurrencePaths substitution typ) :
    ∀ name path, (name, path) ∈ childrenOccurrences front.length types →
      (Term.node symbol (front ++ types.map (instantiate substitution))).atPath path = some (substitution name) := by
  intro name path member
  obtain ⟨index, typ, rest, selected, same, found⟩ := children_origin front.length types name path member
  rw [same, Term.atPath, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map, selected]
  simp only [Option.map_some, Option.bind_some]
  exact checked typ (List.mem_of_getElem? selected) name rest found

private theorem arrow_paths (substitution : String → Term Symbol) (argument result : Ty)
    (first : OccurrencePaths substitution argument) (second : OccurrencePaths substitution result) :
    ∀ name path, (name, path) ∈ shift 1 (occurrences argument) ++ shift 2 (occurrences result) →
      (arrow (instantiate substitution argument) (instantiate substitution result)).atPath path =
        some (substitution name) := by
  have checked : ∀ typ ∈ [argument, result], OccurrencePaths substitution typ := by
    intro typ member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second
  simpa only [arrow, List.length_cons, List.length_nil, childrenOccurrences, List.append_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
    node_paths substitution (literal "->") [.node (literal "(->)") []] [argument, result] checked

/-- Each recorded occurrence selects the same finite image of its encoded key. -/
theorem occurrence_atPath (substitution : String → Term Symbol) (typ : Ty) :
    ∀ name path, (name, path) ∈ occurrences typ →
      (instantiate substitution typ).atPath path = some (substitution name) := by
  change OccurrencePaths substitution typ
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, OccurrencePaths substitution typ) with
  | tVar name =>
      intro key path member
      simp only [occurrences] at member
      have same := List.mem_singleton.mp member
      cases same
      simp only [instantiate, Term.atPath]
  | tFun argument result first second =>
      simpa only [OccurrencePaths, occurrences, instantiate] using
        arrow_paths substitution argument result first second
  | tCons name arguments children =>
      have ordinary (actual : occurrences (.tCons name arguments) = childrenOccurrences 0 arguments)
          (shape : instantiate substitution (.tCons name arguments) =
            .node (literal name) (arguments.map (instantiate substitution))) :
          OccurrencePaths substitution (.tCons name arguments) := by
        intro key path member
        rw [actual] at member
        rw [shape]
        simpa only [List.length_nil, List.nil_append] using
          node_paths substitution (literal name) [] arguments children key path member
      cases arguments with
      | nil =>
          by_cases recognized : isVariableSymbol name = true
          · intro key path member
            simp only [occurrences, recognized, ↓reduceIte] at member
            have same := List.mem_singleton.mp member
            cases same
            simp only [instantiate, recognized, ↓reduceIte, Term.atPath]
          · intro key path member
            simp only [occurrences, recognized, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at member
      | cons first rest =>
          cases rest with
          | nil => exact ordinary (by simp only [occurrences]) (by simp [instantiate])
          | cons second rest =>
              cases rest with
              | cons third tail => exact ordinary (by simp only [occurrences]) (by simp [instantiate])
              | nil =>
                  by_cases alias : name = "Fun"
                  · have both := arrow_paths substitution first second
                      (children first (by simp)) (children second (by simp))
                    simpa only [OccurrencePaths, occurrences, instantiate, alias, ↓reduceIte] using both
                  · exact ordinary (by simp only [occurrences, alias, ↓reduceIte])
                      (by simp only [instantiate, alias, ↓reduceIte, List.map_cons, List.map_nil])
  | nil => rename_i typ member; cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

/-- Uniform images satisfy every equality class generated by the actual scheme. -/
theorem generated_equalities (substitution : String → Term Symbol) (typ : Ty) :
    EqualityNormalize.Satisfies (instantiate substitution typ) (equalityClasses typ) := by
  intro paths included left first right second _different
  obtain ⟨name, _recognized, same⟩ := equalityClasses_origin typ paths included
  subst paths
  exact ⟨substitution name,
    occurrence_atPath substitution typ name left ((mem_pathsOf name typ left).mp first),
    occurrence_atPath substitution typ name right ((mem_pathsOf name typ right).mp second)⟩

private theorem node_member (holds : Guard → Term Symbol → Bool) (name : String) (guard : Guard)
    (children : List (Expr Guard)) (terms : List (Term Symbol))
    (accepted : forest holds [] (mapChildren literal children) terms)
    (held : holds guard (.node (literal name) terms) = true) :
    evaluate holds [] (mapSyntax literal (.node [.mk name guard children])) (.node (literal name) terms) := by
  simp only [mapSyntax, mapEdges]
  rw [evaluate]
  refine ⟨⟨.mk (literal name) guard (mapChildren literal children), List.mem_cons_self⟩, ?_⟩
  rw [edgeMeaning]
  exact ⟨terms, rfl, accepted, held⟩

private theorem mapped_forest (holds : Guard → Term Symbol → Bool) (types : List Ty)
    (plans : Ty → Expr Guard) (substitution : String → Term Symbol)
    (checked : ∀ typ ∈ types,
      evaluate holds [] (mapSyntax literal (plans typ)) (instantiate substitution typ)) :
    forest holds [] (mapChildren literal (types.map plans)) (types.map (instantiate substitution)) := by
  induction types with
  | nil => simp only [List.map_nil, mapChildren, forest]
  | cons first rest ih =>
      simp only [List.map_cons, mapChildren, forest]
      exact ⟨checked first List.mem_cons_self,
        ih (fun typ member => checked typ (List.mem_cons_of_mem _ member))⟩

private theorem arrow_member (holds : Guard → Term Symbol → Bool) (topHeld : ∀ term, holds top term = true)
    (argument result : Expr Guard) (first second : Term Symbol)
    (left : evaluate holds [] (mapSyntax literal argument) first)
    (right : evaluate holds [] (mapSyntax literal result) second) :
    evaluate holds [] (mapSyntax literal (arrowType top argument result)) (arrow first second) := by
  apply node_member holds "->" top [arrowMarker top, argument, result]
    [.node (literal "(->)") [], first, second]
  · simp only [mapChildren, forest]
    exact ⟨node_member holds "(->)" top [] [] (by simp only [mapChildren, forest]) (topHeld _), left, right, True.intro⟩
  · exact topHeld _

private def Admitted (holds : Guard → Term Symbol → Bool) (types : Expr Guard)
    (substitution : String → Term Symbol) (typ : Ty) : Prop :=
  ∀ name path, (name, path) ∈ occurrences typ →
    evaluate holds [] (mapSyntax literal types) (substitution name)

private theorem replace_member (holds : Guard → Term Symbol → Bool) (topHeld : ∀ term, holds top term = true)
    (types : Expr Guard) (substitution : String → Term Symbol) (typ : Ty) :
    Admitted holds types substitution typ →
      evaluate holds [] (mapSyntax literal (replace types typ)) (instantiate substitution typ) := by
  induction typ using Ty.rec
    (motive_2 := fun values => ∀ typ ∈ values, Admitted holds types substitution typ →
      evaluate holds [] (mapSyntax literal (replace types typ)) (instantiate substitution typ)) with
  | tVar name =>
      intro admitted
      simpa only [replace, instantiate] using admitted (variableSymbol name) []
        (by simp only [occurrences]; exact List.mem_cons_self)
  | tFun argument result first second =>
      intro admitted
      simp only [replace, instantiate]
      simp only [Admitted, occurrences] at admitted
      apply arrow_member holds topHeld
      · apply first
        intro name path found
        exact admitted name (1 :: path) (List.mem_append.mpr (Or.inl
          ((shift_member 1 _ name _).mpr ⟨path, rfl, found⟩)))
      · apply second
        intro name path found
        exact admitted name (2 :: path) (List.mem_append.mpr (Or.inr
          ((shift_member 2 _ name _).mpr ⟨path, rfl, found⟩)))
  | tCons name arguments children =>
      intro admitted
      have ordinary (actual : occurrences (.tCons name arguments) = childrenOccurrences 0 arguments) :
          evaluate holds [] (mapSyntax literal (.node [.mk name top (arguments.map (replace types))]))
            (.node (literal name) (arguments.map (instantiate substitution))) := by
        apply node_member holds name top _ _ _ (topHeld _)
        apply mapped_forest
        intro typ included
        apply children typ included
        intro key path found
        obtain ⟨actualPath, member⟩ := child_member 0 arguments typ included key path found
        exact admitted key actualPath (by simpa only [actual] using member)
      cases arguments with
      | nil =>
          by_cases recognized : isVariableSymbol name = true
          · simpa only [replace, instantiate, recognized, ↓reduceIte] using
              admitted name [] (by simp only [occurrences, recognized, ↓reduceIte, List.mem_singleton])
          · simpa only [replace, instantiate, recognized, Bool.false_eq_true, ↓reduceIte, List.map_nil] using
              ordinary (by simp only [occurrences, recognized, Bool.false_eq_true, ↓reduceIte, childrenOccurrences])
      | cons first rest =>
          cases rest with
          | nil => simpa only [replace, instantiate] using ordinary (by simp only [occurrences])
          | cons second rest =>
              cases rest with
              | cons third tail => simpa only [replace, instantiate] using ordinary (by simp only [occurrences])
              | nil =>
                  by_cases alias : name = "Fun"
                  · simp only [replace, instantiate, alias, ↓reduceIte]
                    apply arrow_member holds topHeld
                    · apply children first (by simp)
                      intro key path found
                      apply admitted key (1 :: path)
                      simp only [occurrences, alias, ↓reduceIte]
                      exact List.mem_append.mpr (Or.inl ((shift_member 1 _ key _).mpr ⟨path, rfl, found⟩))
                    · apply children second (by simp)
                      intro key path found
                      apply admitted key (2 :: path)
                      simp only [occurrences, alias, ↓reduceIte]
                      exact List.mem_append.mpr (Or.inr ((shift_member 2 _ key _).mpr ⟨path, rfl, found⟩))
                  · simpa only [replace, instantiate, alias, ↓reduceIte, List.map_cons, List.map_nil] using
                      ordinary (by simp only [occurrences, alias, ↓reduceIte])
  | nil => rename_i typ member admitted; cases member
  | cons first rest own later =>
      rename_i typ member admitted
      rcases List.mem_cons.mp member with rfl | member
      · exact own admitted
      · exact later typ member admitted

private theorem change_guard (holds : Guard → Term Symbol → Bool) (name : String)
    (children : List (Expr Guard)) (term : Term Symbol) (guard : Guard)
    (accepted : evaluate holds [] (mapSyntax literal (.node [.mk name top children])) term)
    (held : holds guard term = true) :
    evaluate holds [] (mapSyntax literal (.node [.mk name guard children])) term := by
  simp only [mapSyntax, mapEdges] at accepted ⊢
  rw [evaluate] at accepted ⊢
  obtain ⟨⟨edge, member⟩, inside⟩ := accepted
  have same := List.mem_singleton.mp member
  cases same
  rw [edgeMeaning] at inside
  obtain ⟨terms, shape, acceptedChildren, _oldGuard⟩ := inside
  refine ⟨⟨.mk (literal name) guard (mapChildren literal children), List.mem_cons_self⟩, ?_⟩
  rw [edgeMeaning]
  exact ⟨terms, shape, acceptedChildren, held⟩

variable [DecidableEq FullSyntax.Formula]

private theorem generated_guard (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (substitution : String → Term Symbol) (typ : Ty) :
    SourceEqualityPCSGuard.holds formulas solver (eqGuard (equalityClasses typ)) (instantiate substitution typ) = true := by
  apply (SourceEqualityPCSGuard.holds_exact formulas solver _ _).mpr
  constructor
  · rw [eqGuard_eq_source]
    exact (SourceEqualityPCSGuard.normalize_sat _ _).mpr (generated_equalities substitution typ)
  · exact ((SourceEqualityPCSGuard.holds_exact formulas solver SourceEqualityConstraintConstructors.top _).mp
      (SourceEqualityPCSConstructors.top_true formulas solver _)).2

/-- A complex scheme accepts its uniform finite instance at every demanded universe key. -/
theorem generalize_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (catalog : List (String × Nat))
    (typ : Ty) (substitution : String → Term Symbol)
    (admitted : ∀ name ∈ variables typ,
      evaluate (SourceEqualityPCSGuard.holds formulas solver) []
        (mapSyntax literal (allTypes top catalog)) (substitution name)) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (generalize (allTypes top catalog) typ)) (instantiate substitution typ) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let types := allTypes top catalog
  have replaced := replace_member holds (SourceEqualityPCSConstructors.top_true formulas solver)
    types substitution typ (fun name path found => admitted name ((mem_variables name typ).mpr ⟨path, found⟩))
  have guarded := generated_guard formulas solver substitution typ
  have lift (name : String) (children : List (Expr Guard))
      (shape : replace types typ = .node [.mk name top children]) (root : rootSymbol typ = name) :
      evaluate holds [] (mapSyntax literal (generalize types typ)) (instantiate substitution typ) := by
    simp only [generalize, shape, finish, root]
    exact change_guard holds name children _ _ (by simpa only [shape] using replaced) guarded
  cases typ with
  | tVar name =>
      simpa only [generalize, replace, types, allTypes, finish] using replaced
  | tFun argument result =>
      exact lift "->" [arrowMarker top, replace types argument, replace types result]
        (by simp only [replace, arrowType]) rfl
  | tCons name arguments =>
      cases arguments with
      | nil =>
          by_cases recognized : isVariableSymbol name = true
          · simpa only [generalize, replace, recognized, ↓reduceIte, types, allTypes, finish] using replaced
          · exact lift name [] (by simp only [replace, recognized, Bool.false_eq_true, ↓reduceIte]) rfl
      | cons first rest =>
          cases rest with
          | nil => exact lift name [replace types first] (by simp [replace]) rfl
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  exact lift name ((first :: second :: third :: tail).map (replace types))
                    (by simp only [replace]) rfl
              | nil =>
                  by_cases alias : name = "Fun"
                  · exact lift "->" [arrowMarker top, replace types first, replace types second]
                      (by simp only [replace, alias, ↓reduceIte, arrowType])
                      (by simp only [rootSymbol, alias, ↓reduceIte])
                  · exact lift name [replace types first, replace types second]
                      (by simp only [replace, alias, ↓reduceIte])
                      (by simp only [rootSymbol, alias, ↓reduceIte])

end MicroCFTA.SourceSynthesisGeneralizeFiniteInstances
