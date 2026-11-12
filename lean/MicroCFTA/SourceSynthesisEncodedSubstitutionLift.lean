import MicroCFTA.SourceSynthesisTypeSubstitutionWitnesses

/-!
# Raw substitutions at discovered source keys

Each occurrence supplies one raw substitution. The key decoder constructs its
encoded substitution. Image admission applies only to keys discovered in the
original scheme. Original constant leaves retain the AliasSafe condition.

These laws concern literal source leaves and size-one terms. They do not define
conventional Program typing or prove its complete source admissibility. The
finite universe, source pruning, relevant winners, and role conditions remain.
-/
namespace MicroCFTA.SourceSynthesisEncodedSubstitutionLift
open Language
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (top variables occurrences childrenOccurrences shift mem_variables)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisSourceTermsTyping (LeafTyping TermsTyping)
open SourceSynthesisTypeSubstitutionWitnesses (substTy AliasSafe)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- Decode the four reserved keys and the ordinary four-character prefix. -/
def decodeVariable : String → String
  | "var1" => "a"
  | "var2" => "b"
  | "var3" => "c"
  | "var4" => "d"
  | key => String.ofList (key.toList.drop 4)

private theorem prefix_ne_reserved (name : String) (last : Char) (different : '_' ≠ last) :
    "var_" ++ name ≠ String.ofList ['v', 'a', 'r', last] := by
  intro same
  have chars := congrArg String.toList same
  simp only [String.toList_append, String.toList_ofList] at chars
  change 'v' :: 'a' :: 'r' :: '_' :: name.toList = ['v', 'a', 'r', last] at chars
  have fourth := congrArg (fun items : List Char => items[3]?) chars
  change some '_' = some last at fourth
  exact different (Option.some.inj fourth)

private theorem decode_prefixed (name : String) : decodeVariable ("var_" ++ name) = name := by
  have first : "var_" ++ name ≠ "var1" := prefix_ne_reserved name '1' (by decide)
  have second : "var_" ++ name ≠ "var2" := prefix_ne_reserved name '2' (by decide)
  have third : "var_" ++ name ≠ "var3" := prefix_ne_reserved name '3' (by decide)
  have fourth : "var_" ++ name ≠ "var4" := prefix_ne_reserved name '4' (by decide)
  simp only [decodeVariable]
  rw [String.toList_append]
  change String.ofList name.toList = name
  exact String.ofList_toList

/-- Decoding recovers every actual raw variable name. -/
theorem decode_variableSymbol (name : String) : decodeVariable (variableSymbol name) = name := by
  by_cases first : name = "a"
  · subst name; rfl
  by_cases second : name = "b"
  · subst name; rfl
  by_cases third : name = "c"
  · subst name; rfl
  by_cases fourth : name = "d"
  · subst name; rfl
  have encoded : variableSymbol name = "var_" ++ name := by
    simp only [variableSymbol]
  rw [encoded]
  exact decode_prefixed name

/-- The actual source encoding does not merge distinct raw variable names. -/
theorem variableSymbol_injective : Function.Injective variableSymbol := by
  intro first second same
  have decoded := congrArg decodeVariable same
  simpa only [decode_variableSymbol] using decoded

private def KeyRange (items : List (String × List Nat)) : Prop :=
  ∀ item ∈ items, variableSymbol (decodeVariable item.1) = item.1

private theorem keys_nil : KeyRange [] := by
  intro item member
  cases member

private theorem keys_shift (index : Nat) {items : List (String × List Nat)}
    (good : KeyRange items) : KeyRange (shift index items) := by
  intro item member
  simp only [shift] at member
  obtain ⟨original, included, same⟩ := List.mem_map.mp member
  subst item
  exact good original included

private theorem keys_append {first second : List (String × List Nat)}
    (left : KeyRange first) (right : KeyRange second) : KeyRange (first ++ second) := by
  intro item member
  rcases List.mem_append.mp member with member | member
  · exact left item member
  · exact right item member

private theorem keys_children (types : List Ty) :
    (∀ typ ∈ types, KeyRange (occurrences typ)) →
      ∀ index, KeyRange (childrenOccurrences index types) := by
  induction types with
  | nil =>
      intro _good index
      simpa only [childrenOccurrences] using keys_nil
  | cons first rest later =>
      intro good index
      simp only [childrenOccurrences]
      exact keys_append (keys_shift index (good first (by simp)))
        (later (fun typ member => good typ (List.mem_cons_of_mem first member)) (index + 1))

private theorem occurrence_keys (scheme : Ty) : AliasSafe scheme → KeyRange (occurrences scheme) := by
  induction scheme using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, AliasSafe typ → KeyRange (occurrences typ)) with
  | tVar name =>
      intro _safe item member
      simp only [occurrences, List.mem_singleton] at member
      subst item
      change variableSymbol (decodeVariable (variableSymbol name)) = variableSymbol name
      rw [decode_variableSymbol]
  | tFun argument result first second =>
      intro safe
      simp only [AliasSafe] at safe
      simpa only [occurrences] using
        keys_append (keys_shift 1 (first safe.1)) (keys_shift 2 (second safe.2))
  | tCons name arguments children =>
      intro safe
      simp only [AliasSafe] at safe
      have good : ∀ typ ∈ arguments, KeyRange (occurrences typ) :=
        fun typ member => children typ member (safe.2 typ member)
      have ordinary := keys_children arguments good 0
      cases arguments with
      | nil =>
          have notVariable := safe.1 rfl
          simpa only [occurrences, notVariable, Bool.false_eq_true, ↓reduceIte] using keys_nil
      | cons first rest =>
          cases rest with
          | nil => simpa only [occurrences] using ordinary
          | cons second rest =>
              cases rest with
              | cons third tail => simpa only [occurrences] using ordinary
              | nil =>
                  by_cases alias : name = "Fun"
                  · have left := good first (by simp)
                    have right := good second (by simp)
                    simpa only [occurrences, alias, ↓reduceIte] using
                      keys_append (keys_shift 1 left) (keys_shift 2 right)
                  · simpa only [occurrences, alias, ↓reduceIte] using ordinary
  | nil =>
      rename_i typ member _safe
      cases member
  | cons first rest own later =>
      rename_i typ member safe
      rcases List.mem_cons.mp member with rfl | member
      · exact own safe
      · exact later typ member safe

/-- Every discovered key of an alias-safe scheme comes from its decoded raw name. -/
theorem variable_key_roundtrip (scheme : Ty) (safe : AliasSafe scheme) (key : String)
    (member : key ∈ variables scheme) : variableSymbol (decodeVariable key) = key := by
  obtain ⟨path, present⟩ := (mem_variables key scheme).mp member
  exact occurrence_keys scheme safe (key, path) present

/-- Construct one occurrence's encoded substitution from its raw substitution. -/
def liftSubstitution (rho : String → Ty) (key : String) : Term Symbol :=
  rigidTerm (rho (decodeVariable key))

/-- The constructed substitution has the required image at each raw variable. -/
theorem liftSubstitution_variable (rho : String → Ty) (name : String) :
    liftSubstitution rho (variableSymbol name) = rigidTerm (rho name) := by
  simp only [liftSubstitution, decode_variableSymbol]

/-- Image admission is required only for raw names whose keys the scheme discovers. -/
theorem liftSubstitution_images (catalog : List (String × Nat)) (scheme : Ty)
    (rho : String → Ty) (safe : AliasSafe scheme)
    (admitted : ∀ name, variableSymbol name ∈ variables scheme → TypeIn catalog (rigidTerm (rho name))) :
    ∀ key ∈ variables scheme, TypeIn catalog (liftSubstitution rho key) := by
  intro key member
  apply admitted (decodeVariable key)
  rw [variable_key_roundtrip scheme safe key member]
  exact member

/-- A raw substitution supplies a conventional component leaf without an encoded supplier. -/
theorem component_instance_leaf (catalog : List (String × Nat)) (name : String) (scheme : Ty)
    (rho : String → Ty) (safe : AliasSafe scheme)
    (admitted : ∀ raw, variableSymbol raw ∈ variables scheme → TypeIn catalog (rigidTerm (rho raw))) :
    LeafTyping catalog (component (allTypes top catalog) name scheme) (.var name)
      (rigidTerm (substTy rho scheme)) (.node (literal name) [rigidTerm (substTy rho scheme)]) := by
  exact SourceSynthesisTypeSubstitutionWitnesses.component_instance_leaf catalog name scheme rho
    (liftSubstitution rho) safe (fun raw _ => liftSubstitution_variable rho raw)
    (liftSubstitution_images catalog scheme rho safe admitted)

/-- An actual group binding supplies size one from its own raw substitution. -/
theorem group_instance_terms (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Ty × List String) (binding : entry ∈ lib.libraryGroups)
    (rho : String → Ty) (safe : AliasSafe entry.2.1)
    (admitted : ∀ raw, variableSymbol raw ∈ variables entry.2.1 →
      TypeIn (constructorCatalog lib query) (rigidTerm (rho raw))) :
    TermsTyping lib query asArgument 1 (.var entry.1) (rigidTerm (substTy rho entry.2.1))
      (.node (literal entry.1) [rigidTerm (substTy rho entry.2.1)]) := by
  exact SourceSynthesisTypeSubstitutionWitnesses.component_instance_terms lib query asArgument entry
    binding rho (liftSubstitution rho) safe (fun raw _ => liftSubstitution_variable rho raw)
    (liftSubstitution_images (constructorCatalog lib query) entry.2.1 rho safe admitted)

/-- An actual argument-only binding supplies size one at the required argument role. -/
theorem argumentOnly_instance_terms (lib : Library) (query : Query)
    (entry : String × Ty) (binding : entry ∈ lib.libraryArgumentOnly)
    (rho : String → Ty) (safe : AliasSafe entry.2)
    (admitted : ∀ raw, variableSymbol raw ∈ variables entry.2 →
      TypeIn (constructorCatalog lib query) (rigidTerm (rho raw))) :
    TermsTyping lib query true 1 (.var entry.1) (rigidTerm (substTy rho entry.2))
      (.node (literal entry.1) [rigidTerm (substTy rho entry.2)]) := by
  exact SourceSynthesisTypeSubstitutionWitnesses.argumentOnly_instance_terms lib query entry binding
    rho (liftSubstitution rho) safe (fun raw _ => liftSubstitution_variable rho raw)
    (liftSubstitution_images (constructorCatalog lib query) entry.2 rho safe admitted)

end MicroCFTA.SourceSynthesisEncodedSubstitutionLift
