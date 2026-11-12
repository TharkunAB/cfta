import MicroCFTA.SourceSynthesisTypeSubstitutionWitnesses

/-!
# Independent ordinary typing of synthesis Programs

Component occurrences instantiate their raw schemes independently. Query
types remain rigid. Ordinary type equality normalizes only the documented
Fun/2 arrow alias. Group representatives remain literal Program names.

The typing rules contain no universe, pruning, role, argument-count, or source
table conditions. Source admission remains a separate obligation. Rigid
encoding preserves this type equality. Its converse is false on raw inputs.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryTyping
open Language
open SourceSynthesisTypeSyntax
open SourceSynthesisProgramTermSize (Program)
open SourceSynthesisTypeSubstitutionWitnesses (substTy)
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- Normalize the two-argument Fun alias and retain every other constructor tag. -/
def normalizeTy : Ty → Ty
  | .tVar name => .tVar name
  | .tFun argument result => .tFun (normalizeTy argument) (normalizeTy result)
  | .tCons name [argument, result] =>
      if name = "Fun" then .tFun (normalizeTy argument) (normalizeTy result)
      else .tCons name [normalizeTy argument, normalizeTy result]
  | .tCons name children => .tCons name (children.map normalizeTy)

/-- Ordinary equality identifies only types with the same normalized raw syntax. -/
def Equivalent (first second : Ty) : Prop := normalizeTy first = normalizeTy second

/-- Ordinary named lookup reads the last matching query binding. -/
def queryLookup (arguments : List (String × Ty)) (name : String) : Option Ty :=
  List.lookup name arguments.reverse

/-- Ordinary typing uses raw instances, rigid query bindings, and application. -/
inductive Typed (lib : Library) (query : Query) : Program → Ty → Prop where
  | group (entry : String × Ty × List String) (binding : entry ∈ lib.libraryGroups)
      (rho : String → Ty) :
      Typed lib query (.var entry.1) (substTy rho entry.2.1)
  | argumentOnly (entry : String × Ty) (binding : entry ∈ lib.libraryArgumentOnly)
      (rho : String → Ty) :
      Typed lib query (.var entry.1) (substTy rho entry.2)
  | queryArgument {name : String} {typ : Ty}
      (found : queryLookup query.queryArguments name = some typ) :
      Typed lib query (.var name) typ
  | application {function argument : Program} {domain codomain : Ty}
      (first : Typed lib query function (.tFun domain codomain))
      (second : Typed lib query argument domain) :
      Typed lib query (.app function argument) codomain
  | conversion {program : Program} {first second : Ty}
      (typed : Typed lib query program first) (same : Equivalent first second) :
      Typed lib query program second

/-- The current rigid encoder preserves normalization of the documented arrow alias. -/
theorem rigidTerm_normalize (typ : Ty) : rigidTerm (normalizeTy typ) = rigidTerm typ := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, rigidTerm (normalizeTy typ) = rigidTerm typ) with
  | tVar name => simp only [normalizeTy]
  | tFun argument result first second =>
      simp only [normalizeTy, rigidTerm, first, second]
  | tCons name arguments children =>
      have mapped : (arguments.map normalizeTy).map rigidTerm = arguments.map rigidTerm := by
        rw [List.map_map]
        apply List.map_congr_left
        intro typ member
        exact children typ member
      have ordinary := congrArg (fun terms => Term.node (literal name) terms) mapped
      cases arguments with
      | nil => simp only [normalizeTy, rigidTerm, List.map_nil]
      | cons first rest =>
          cases rest with
          | nil =>
              simpa only [normalizeTy, rigidTerm, List.map_cons, List.map_nil] using ordinary
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  simpa only [normalizeTy, rigidTerm, List.map_cons, List.map_nil] using ordinary
              | nil =>
                  have firstEq := children first (by simp)
                  have secondEq := children second (by simp)
                  by_cases alias : name = "Fun"
                  · subst name
                    simp only [normalizeTy, rigidTerm, ↓reduceIte, firstEq, secondEq]
                  · simpa only [normalizeTy, rigidTerm, alias, ↓reduceIte, List.map_cons,
                      List.map_nil] using ordinary
  | nil =>
      rename_i typ member
      cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

/-- Ordinary equality implies equal rigid encodings without assuming reflection. -/
theorem equivalent_rigidTerm (first second : Ty) (same : Equivalent first second) :
    rigidTerm first = rigidTerm second := by
  change normalizeTy first = normalizeTy second at same
  have encoded := congrArg rigidTerm same
  rw [rigidTerm_normalize, rigidTerm_normalize] at encoded
  exact encoded

/-- The literal Fun constructor with two arguments has its documented arrow type. -/
theorem funAlias_equivalent (argument result : Ty) :
    Equivalent (.tCons "Fun" [argument, result]) (.tFun argument result) := by
  simp only [Equivalent, normalizeTy, ↓reduceIte]

/-- A successful ordinary query lookup names an actual input binding. -/
theorem queryLookup_member (arguments : List (String × Ty)) (name : String) (typ : Ty)
    (found : queryLookup arguments name = some typ) : (name, typ) ∈ arguments := by
  change arguments.reverse.lookup name = some typ at found
  obtain ⟨_before, _after, same, _earlier⟩ := List.lookup_eq_some_iff.mp found
  have present : (name, typ) ∈ arguments.reverse := by
    rw [same]
    exact List.mem_append.mpr (.inr List.mem_cons_self)
  exact List.mem_reverse.mp present

/-- A function written with the Fun/2 alias supports ordinary application. -/
theorem Typed.application_funAlias {lib : Library} {query : Query}
    {function argument : Program} {domain codomain : Ty}
    (first : Typed lib query function (.tCons "Fun" [domain, codomain]))
    (second : Typed lib query argument domain) :
    Typed lib query (.app function argument) codomain :=
  .application (.conversion first (funAlias_equivalent domain codomain)) second

end MicroCFTA.SourceSynthesisOrdinaryTyping
