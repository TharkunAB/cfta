import MicroCFTA.SourceSynthesisTypeSyntax
import MicroCFTA.SourceEqualityConstraintConstructors

/-!
# FirstOrder generalization of finite original types

This file follows Gen.Synthesis.generalize and isVariable. It retains the
current finite child order and the arrow marker at child zero. Replacements
do not traverse the supplied type universe. Equality payloads use the closed
input-derived reference normalizer and equal the checked source payload.
Native array-work realization is separate. The result is a constructor-instruction syntax stage.
Native smart construction can remove rows or binders. Its graph readback,
later projection, and intersection correspondence are separate obligations.
-/
namespace MicroCFTA.SourceSynthesisGeneralizeSyntax
open SourceSynthesisTypeSyntax (Ty Expr variableSymbol arrowMarker arrowType)
open InternedNestedConstruction (Syntax EdgeSyntax Scoped ManyScoped EdgesScoped)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)

/-- Keep the actual equality payload and complete guard fields. -/
abbrev Guard := SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Ordinary type-pattern edges have the source noConstraint value. -/
def top : Guard := SourceEqualityConstraintConstructors.top

/-- Compute the checked equality payload with the derived normalization bound. -/
def eqGuard (classes : List (List (List Nat))) : Guard :=
  ⟨SymbolicEqualityBridge.resultClasses
    (EqualityNormalize.mkEqConstraints (EqualityTermination.normalizationBound classes) classes), .top⟩

/-- Native recognition depends on the leaf symbol, not on the source Ty tag. -/
def isVariableSymbol (name : String) : Bool :=
  decide (name ∈ ["var1", "var2", "var3", "var4"]) || name.startsWith "var_"

/-- Every encoded source type variable passes native symbol recognition. -/
theorem variableSymbol_recognized (name : String) : isVariableSymbol (variableSymbol name) = true := by
  have prefixed : ("var_" ++ name).startsWith "var_" = true := by
    apply String.startsWith_string_iff.mpr
    exact ⟨name.toList, by simp⟩
  by_cases first : name = "a"
  · subst name; rfl
  by_cases second : name = "b"
  · subst name; rfl
  by_cases third : name = "c"
  · subst name; rfl
  by_cases fourth : name = "d"
  · subst name; rfl
  simp only [variableSymbol, isVariableSymbol, prefixed, Bool.or_true]

/-- Prefix each occurrence path by its actual child index. -/
def shift (index : Nat) (items : List (String × List Nat)) : List (String × List Nat) :=
  items.map fun item => (item.1, index :: item.2)

mutual
/-- Read recognized original leaves in finite source child order. -/
def occurrences : Ty → List (String × List Nat)
  | .tVar name => [(variableSymbol name, [])]
  | .tFun argument result => shift 1 (occurrences argument) ++ shift 2 (occurrences result)
  | .tCons name [] => if isVariableSymbol name then [(name, [])] else []
  | .tCons name [argument, result] =>
      if name = "Fun" then shift 1 (occurrences argument) ++ shift 2 (occurrences result)
      else childrenOccurrences 0 [argument, result]
  | .tCons _ arguments => childrenOccurrences 0 arguments
termination_by typ => sizeOf typ
decreasing_by all_goals simp_wf; all_goals omega

/-- Ordinary constructor arguments start at child zero. -/
def childrenOccurrences (index : Nat) : List Ty → List (String × List Nat)
  | [] => []
  | first :: rest => shift index (occurrences first) ++ childrenOccurrences (index + 1) rest
termination_by types => sizeOf types
decreasing_by all_goals simp_wf; all_goals omega
end

/-- Keep each recognized leaf shape once, at its first occurrence. -/
def variables (typ : Ty) : List String := (occurrences typ).map Prod.fst |>.eraseDups

/-- Read all occurrences of one original variable-shaped leaf. -/
def pathsOf (name : String) (typ : Ty) : List (List Nat) :=
  (occurrences typ).filterMap fun item => if item.1 = name then some item.2 else none

/-- The normalizer receives one ordered path class per recognized leaf shape. -/
def equalityClasses (typ : Ty) : List (List (List Nat)) :=
  (variables typ).map fun name => pathsOf name typ

/-- Retain the original outer symbol, including the two-argument Fun alias. -/
def rootSymbol : Ty → String
  | .tVar name => variableSymbol name
  | .tFun _ _ => "->"
  | .tCons name [_, _] => if name = "Fun" then "->" else name
  | .tCons name _ => name

/-- Replace recognized original leaves without descending into inserted syntax. -/
def replace (types : Expr Guard) : Ty → Expr Guard
  | .tVar _ => types
  | .tFun argument result => arrowType top (replace types argument) (replace types result)
  | .tCons name [] => if isVariableSymbol name then types else .node [.mk name top []]
  | .tCons name [argument, result] =>
      if name = "Fun" then arrowType top (replace types argument) (replace types result)
      else .node [.mk name top [replace types argument, replace types result]]
  | .tCons name arguments => .node [.mk name top (arguments.map (replace types))]

/-- Follow the native outer match after the simultaneous replacement. -/
def finish (symbol : String) (classes : List (List (List Nat))) : Expr Guard → Expr Guard
  | .node [.mk _ _ children] => .node [.mk symbol (eqGuard classes) children]
  | other => other

/-- Generalize a finite original type before native constructor normalization. -/
def generalize (types : Expr Guard) (typ : Ty) : Expr Guard :=
  finish (rootSymbol typ) (equalityClasses typ) (replace types typ)

/-- The computed reference run returns exactly the checked source-normalizer payload. -/
theorem eqGuard_eq_source (classes : List (List (List Nat))) :
    eqGuard classes = ⟨SourceCompactGuards.normalize classes, .top⟩ := by
  simp only [eqGuard, SourceCompactGuards.normalize, SourceCompactGuards.arrayNormalize_eq]

/-- Every normalized output payload has active equality classes. -/
theorem eqGuard_active (classes : List (List (List Nat))) :
    SourceCompactGuards.ActiveOption (eqGuard classes).equalities := by
  rw [eqGuard_eq_source]
  exact SourceCompactGuards.normalize_active classes

/-- The generalizer never introduces a residual formula. -/
theorem eqGuard_residual (classes : List (List (List Nat))) : (eqGuard classes).guard = .top := rfl

/-- Variable-shape discovery has no repeated symbols. -/
theorem variables_distinct (typ : Ty) : (variables typ).Nodup :=
  SymbolicDriver.eraseDups_nodup _

/-- Discovery contains exactly the symbols of recognized original occurrences. -/
theorem mem_variables (name : String) (typ : Ty) :
    name ∈ variables typ ↔ ∃ path, (name, path) ∈ occurrences typ := by
  simp only [variables, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨⟨symbol, path⟩, member, same⟩
    cases same
    exact ⟨path, member⟩
  · rintro ⟨path, member⟩
    exact ⟨(name, path), member, rfl⟩

/-- Each equality-class path is an exact occurrence of its own leaf shape. -/
theorem mem_pathsOf (name : String) (typ : Ty) (path : List Nat) :
    path ∈ pathsOf name typ ↔ (name, path) ∈ occurrences typ := by
  simp only [pathsOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨symbol, found⟩, member, selected⟩
    dsimp only at selected
    split at selected
    · rename_i same
      subst symbol
      have identical := Option.some.inj selected
      subst found
      exact member
    · cases selected
  · intro member
    exact ⟨(name, path), member, by simp⟩

/-- Every discovered variable has a nonempty occurrence class. -/
theorem pathsOf_nonempty (name : String) (typ : Ty) (member : name ∈ variables typ) :
    pathsOf name typ ≠ [] := by
  obtain ⟨path, found⟩ := (mem_variables name typ).mp member
  have present := (mem_pathsOf name typ path).mpr found
  intro empty
  simp only [empty, List.not_mem_nil] at present

/-- Every raw equality class comes from one recognized original leaf shape. -/
theorem equalityClasses_origin (typ : Ty) (paths : List (List Nat))
    (member : paths ∈ equalityClasses typ) :
    ∃ name ∈ variables typ, paths = pathsOf name typ := by
  obtain ⟨name, included, same⟩ := List.mem_map.mp member
  exact ⟨name, included, same.symm⟩

private theorem paths_shift (name : String) (index : Nat) (items : List (String × List Nat)) :
    (shift index items).filterMap (fun item => if item.1 = name then some item.2 else none) =
      (items.filterMap fun item => if item.1 = name then some item.2 else none).map (index :: ·) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨symbol, path⟩
      simp only [shift] at ih ⊢
      by_cases same : symbol = name <;> simp [same, ih]

/-- The arrow marker shifts type occurrences to children one and two. -/
theorem pathsOf_arrow (name : String) (argument result : Ty) :
    pathsOf name (.tFun argument result) =
      (pathsOf name argument).map (1 :: ·) ++ (pathsOf name result).map (2 :: ·) := by
  simp only [pathsOf, occurrences, List.filterMap_append, paths_shift]

/-- The Fun constructor alias has the same shifted paths as a literal arrow. -/
theorem pathsOf_fun_alias (name : String) (argument result : Ty) :
    pathsOf name (.tCons "Fun" [argument, result]) = pathsOf name (.tFun argument result) := by
  simp only [pathsOf, occurrences, ↓reduceIte]

/-- A variable-shaped constructor leaf is recognized even without a TVar tag. -/
theorem occurrences_variable_constructor (name : String) (recognized : isVariableSymbol name = true) :
    occurrences (.tCons name []) = [(name, [])] := by
  simp only [occurrences, recognized, ↓reduceIte]

/-- Rigid type variables and matching constructor leaves share one source node shape. -/
theorem variable_shape_alias :
    variables (.tFun (.tVar "a") (.tCons "var1" [])) = ["var1"] := by
  simp [variables, occurrences, shift, variableSymbol, isVariableSymbol]
  decide

/-- A replacement is returned directly, including any inserted Mu binder. -/
theorem replace_variable (types : Expr Guard) (name : String) :
    replace types (.tVar name) = types := by
  simp only [replace]

/-- Native leaf recognition also replaces variable-shaped constructor leaves. -/
theorem replace_variable_constructor (types : Expr Guard) (name : String)
    (recognized : isVariableSymbol name = true) : replace types (.tCons name []) = types := by
  simp only [replace, recognized, ↓reduceIte]

/-- A variable-shaped nonleaf constructor is not a native variable. -/
theorem replace_unary_constructor (types : Expr Guard) (name : String) (argument : Ty) :
    replace types (.tCons name [argument]) = .node [.mk name top [replace types argument]] := by
  simp only [replace, List.map_cons, List.map_nil]

/-- A supplied Mu is not traversed or annotated by variable replacement. -/
theorem generalize_variable_mu (name : String) (smart : Bool) (body : Expr Guard) :
    generalize (.binder smart body) (.tVar name) = .binder smart body := by
  simp only [generalize, replace, finish]

/-- The one-row outer case restores the original symbol and installs its normalized classes. -/
theorem generalize_of_node (types : Expr Guard) (typ : Ty) (name : String) (old : Guard)
    (children : List (Expr Guard)) (mapped : replace types typ = .node [.mk name old children]) :
    generalize types typ = .node [.mk (rootSymbol typ) (eqGuard (equalityClasses typ)) children] := by
  simp only [generalize, mapped, finish]

private def Annotations (types expression : Expr Guard) : Prop :=
  ∀ guard ∈ guards expression, guard = top ∨ guard ∈ guards types

private theorem children_annotations (types : Expr Guard) (children : List (Expr Guard))
    (checked : ∀ child ∈ children, Annotations types child) :
    ∀ guard ∈ childGuards children, guard = top ∨ guard ∈ guards types := by
  induction children with
  | nil => simp only [childGuards, List.not_mem_nil, false_implies, implies_true]
  | cons first rest ih =>
      intro guard member
      rcases List.mem_append.mp member with head | tail
      · exact checked first List.mem_cons_self guard head
      · exact ih (fun child present => checked child (List.mem_cons_of_mem _ present)) guard tail

private theorem node_annotations (types : Expr Guard) (symbol : String) (children : List (Expr Guard))
    (checked : ∀ child ∈ children, Annotations types child) :
    Annotations types (.node [.mk symbol top children]) := by
  intro guard member
  simp only [guards, edgeGuards, List.append_nil, List.mem_cons] at member
  rcases member with rfl | child
  · exact .inl rfl
  · exact children_annotations types children checked guard child

private theorem arrow_annotations (types argument result : Expr Guard)
    (first : Annotations types argument) (second : Annotations types result) :
    Annotations types (arrowType top argument result) := by
  apply node_annotations
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact node_annotations types "(->)" [] (by simp)
  · exact first
  · exact second

/-- All replacement guards come from supplied syntax or from plain finite pattern edges. -/
theorem replace_guards (types : Expr Guard) (typ : Ty) :
    ∀ guard ∈ guards (replace types typ), guard = top ∨ guard ∈ guards types := by
  have inserted : Annotations types types := fun _ member => .inr member
  change Annotations types (replace types typ)
  induction typ using Ty.rec
    (motive_2 := fun typesList => ∀ typ ∈ typesList, Annotations types (replace types typ)) with
  | tVar _ => simpa only [replace] using inserted
  | tFun argument result first second =>
      simpa only [replace] using arrow_annotations types _ _ first second
  | tCons name arguments children =>
      have ordinary : Annotations types (.node [.mk name top (arguments.map (replace types))]) := by
        apply node_annotations
        intro child member
        obtain ⟨typ, included, rfl⟩ := List.mem_map.mp member
        exact children typ included
      cases arguments with
      | nil =>
          by_cases recognized : isVariableSymbol name = true
          · simpa only [replace, recognized, ↓reduceIte] using inserted
          · simpa only [replace, recognized, Bool.false_eq_true, ↓reduceIte, List.map_nil] using ordinary
      | cons first rest =>
          cases rest with
          | nil => simpa only [replace] using ordinary
          | cons second rest =>
              cases rest with
              | cons third tail => simpa only [replace] using ordinary
              | nil =>
                  by_cases alias : name = "Fun"
                  · subst name
                    simpa only [replace, ↓reduceIte] using arrow_annotations types _ _
                      (children first (by simp)) (children second (by simp))
                  · simpa only [replace, alias, ↓reduceIte, List.map_cons, List.map_nil] using ordinary
  | nil => rename_i typ member; cases member
  | cons typ typesList own rest =>
      rename_i other member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact rest other member

private theorem finish_guards (symbol : String) (classes : List (List (List Nat))) (mapped : Expr Guard)
    (guard : Guard) (member : guard ∈ guards (finish symbol classes mapped)) :
    guard = eqGuard classes ∨ guard ∈ guards mapped := by
  cases mapped with
  | empty | var => cases member
  | union | binder => exact .inr member
  | node rows =>
      cases rows with
      | nil => cases member
      | cons first rest =>
          cases first with
          | mk oldSymbol old children =>
              cases rest with
              | cons second tail => exact .inr member
              | nil =>
                  simp only [finish, guards, edgeGuards, List.append_nil, List.mem_cons] at member
                  rcases member with same | inherited
                  · exact .inl same
                  · exact .inr (by simp only [guards, edgeGuards, List.append_nil, List.mem_cons]; exact .inr inherited)

/-- The only new non-Top pattern annotation is at the finite original root. -/
theorem generalize_guards (types : Expr Guard) (typ : Ty) (guard : Guard)
    (member : guard ∈ guards (generalize types typ)) :
    guard = eqGuard (equalityClasses typ) ∨ guard = top ∨ guard ∈ guards types := by
  rcases finish_guards (rootSymbol typ) (equalityClasses typ) (replace types typ) guard member with own | inherited
  · exact .inl own
  · exact .inr (replace_guards types typ guard inherited)

end MicroCFTA.SourceSynthesisGeneralizeSyntax
