import MicroCFTA.BinderLanguage

/-!
# Language preservation for prepared recursive substitution

The source substitutes free references and masks each enclosing binder.
Global fresh binder identities prevent a replacement from being captured.
The theorem states that requirement on each actual replacement explicitly.
-/
namespace MicroCFTA.BinderLanguage
open Language Binding

mutual
  /-- All bound reference identities in a finite shape. -/
  def bound : Shape Item → List Nat
    | .empty | .ref _ => []
    | .branch _ children | .alternatives children => boundList children
    | .binder name body => name :: bound body

  /-- Bound reference identities in a child forest. -/
  def boundList : List (Shape Item) → List Nat
    | [] => []
    | first :: rest => bound first ++ boundList rest
end

/-- No replacement contains a free reference that the target shape would capture. -/
def Fresh (substitution : Environment (Payload Symbol)) (names : List Nat) : Prop :=
  ∀ bound ∈ names, ∀ name replacement, substitution name = some replacement → bound ∉ free replacement

/-- Interpret simultaneous substitutions in the original language environment. -/
def substitutedEnv (environment : Env Symbol) (substitution : Environment (Payload Symbol)) : Env Symbol :=
  fun name => match substitution name with
    | none => environment name
    | some replacement => meaning environment replacement

/-- Masking cannot add or change a replacement. -/
theorem mask_original (substitution : Environment Item) (bound name : Nat) (replacement : Shape Item)
    (found : mask substitution bound name = some replacement) : substitution name = some replacement := by
  by_cases same : name = bound
  · simp [mask, same] at found
  · simpa [mask, same] using found

/-- Freshness remains valid after masking a binder's local name. -/
theorem fresh_mask (substitution : Environment (Payload Symbol)) (name : Nat) (names : List Nat)
    (fresh : Fresh substitution names) : Fresh (mask substitution name) names := by
  intro bound member other replacement found
  exact fresh bound member other replacement (mask_original substitution name other replacement found)

/-- Masked substitution and semantic binding commute under the source freshness condition. -/
theorem environment_bind (environment : Env Symbol) (substitution : Environment (Payload Symbol))
    (name : Nat) (value : Lang Symbol)
    (fresh : ∀ other replacement, substitution other = some replacement → name ∉ free replacement) :
    substitutedEnv (bind environment name value) (mask substitution name) =
      bind (substitutedEnv environment substitution) name value := by
  funext other
  by_cases same : other = name
  · simp [substitutedEnv, mask, bind, same]
  · simp only [substitutedEnv, mask, bind, ite_eq_right same]
    cases found : substitution other with
    | none => rfl
    | some replacement =>
        apply meaning_congr
        intro reference present
        have different : reference ≠ name := fun equal => fresh other replacement found (equal ▸ present)
        simp [bind, different]

/-- The prepared source list plan preserves the exact child order. -/
theorem substituteList_map (substitution : Environment Item) (shapes : List (Shape Item)) :
    substituteList substitution shapes = shapes.map (substitute substitution) := by
  induction shapes with
  | nil => rfl
  | cons first rest ih => simp only [substituteList, List.map_cons, ih]

/-- Childwise semantic substitution gives the entire forest substitution law. -/
theorem forest_substitute (shapes : List (Shape (Payload Symbol))) (environment : Env Symbol)
    (substitution : Environment (Payload Symbol))
    (each : ∀ shape ∈ shapes, meaning environment (substitute substitution shape) =
      meaning (substitutedEnv environment substitution) shape)
    (terms : List (Term Symbol)) :
    forest environment (substituteList substitution shapes) terms ↔
      forest (substitutedEnv environment substitution) shapes terms := by
  induction shapes generalizing terms with
  | nil => cases terms <;> simp only [substituteList, forest]
  | cons first rest ih =>
      cases terms with
      | nil => simp only [substituteList, forest]
      | cons term terms =>
          simp only [substituteList, forest, each first (by simp),
            ih (fun shape member => each shape (by simp [member])) terms]

/-- Prepared simultaneous substitution has the exact capture-free language semantics. -/
theorem substitution_exact (shape : Shape (Payload Symbol)) (environment : Env Symbol)
    (substitution : Environment (Payload Symbol)) (fresh : Fresh substitution (bound shape)) :
    meaning environment (substitute substitution shape) = meaning (substitutedEnv environment substitution) shape := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ environment : Env Symbol, ∀ substitution : Environment (Payload Symbol),
      Fresh substitution (boundList shapes) → ∀ shape ∈ shapes,
      meaning environment (substitute substitution shape) = meaning (substitutedEnv environment substitution) shape)
    generalizing environment substitution with
  | empty => simp only [substitute, meaning]
  | ref name =>
      cases found : substitution name <;> simp [substitute, substitutedEnv, meaning, found]
  | branch payload children ih =>
      funext term
      simp only [substitute, meaning]
      simp only [forest_substitute children environment substitution (ih environment substitution fresh)]
  | alternatives edges ih =>
      funext term
      apply propext
      simp only [substitute, meaning]
      constructor
      · rintro ⟨⟨edge, member⟩, accepted⟩
        rw [substituteList_map] at member
        obtain ⟨original, present, equal⟩ := List.mem_map.mp member
        subst edge
        exact ⟨⟨original, present⟩, by rw [← ih environment substitution fresh original present]; exact accepted⟩
      · rintro ⟨⟨edge, member⟩, accepted⟩
        refine ⟨⟨substitute substitution edge, ?_⟩, ?_⟩
        · rw [substituteList_map]; exact List.mem_map.mpr ⟨edge, member, rfl⟩
        · rw [ih environment substitution fresh edge member]; exact accepted
  | binder name body ih =>
      simp only [substitute, meaning]
      apply least_congr
      intro value term
      have innerFresh : Fresh (mask substitution name) (bound body) :=
        fresh_mask substitution name _ (fun binderName member => fresh binderName (by simp [bound, member]))
      rw [ih (bind environment name value) (mask substitution name) innerFresh]
      rw [environment_bind environment substitution name value
        (fun other replacement found => fresh name (by simp [bound]) other replacement found)]
  | nil => rename_i environment substitution fresh shape member; simp at member
  | cons child rest ih ihtail =>
      rename_i environment substitution fresh shape member
      rcases List.mem_cons.mp member with rfl | member
      · exact ih environment substitution (fun name present => fresh name (by simp [boundList, present]))
      · exact ihtail environment substitution (fun name present => fresh name (by simp [boundList, present])) shape member

/-- Preparing the plan once preserves the same complete term language. -/
theorem prepared_exact (shape : Shape (Payload Symbol)) (environment : Env Symbol)
    (substitution : Environment (Payload Symbol)) (fresh : Fresh substitution (bound shape)) :
    meaning environment (prepare shape substitution) = meaning (substitutedEnv environment substitution) shape := by
  rw [prepare_correct]
  exact substitution_exact shape environment substitution fresh

/-- The single-entry environment used by the public `substFree` operation. -/
def single (name : Nat) (replacement : Shape (Payload Symbol)) : Environment (Payload Symbol) :=
  fun other => if other = name then some replacement else none

/-- A single syntactic replacement has exactly one semantic environment update. -/
theorem single_environment (environment : Env Symbol) (name : Nat) (replacement : Shape (Payload Symbol)) :
    substitutedEnv environment (single name replacement) = bind environment name (meaning environment replacement) := by
  funext other
  by_cases same : other = name <;> simp [substitutedEnv, single, bind, same]

/-- The source's self-unfolding substitution preserves the recursive language. -/
theorem unfold_substitution (environment : Env Symbol) (name : Nat) (body : Shape (Payload Symbol))
    (fresh : Fresh (single name (.binder name body)) (bound body)) :
    meaning environment (substitute (single name (.binder name body)) body) =
      meaning environment (.binder name body) := by
  rw [substitution_exact body environment _ fresh, single_environment]
  funext term
  exact propext (binder_unfold environment name body term).symm

/-- Closed replacement shapes meet the required freshness condition at every binder. -/
theorem closed_prepared (shape : Shape (Payload Symbol)) (environment : Env Symbol)
    (substitution : Environment (Payload Symbol))
    (closed : ∀ name replacement, substitution name = some replacement → free replacement = []) :
    meaning environment (prepare shape substitution) = meaning (substitutedEnv environment substitution) shape := by
  apply prepared_exact
  intro binder _ name replacement found
  simp [closed name replacement found]

/-- Omitting freshness can capture a free reference and remove a valid term. -/
theorem capture_requires_freshness :
    let environment : Env Nat := fun name term => name = 0 ∧ term = .node 0 []
    let shape : Shape (Payload Nat) := .binder 0 (.ref 1)
    let replacement := single 1 (.ref 0 : Shape (Payload Nat))
    ¬ meaning environment (substitute replacement shape) (.node 0 []) ∧
      meaning (substitutedEnv environment replacement) shape (.node 0 []) := by
  dsimp only
  constructor
  · have equal : substitute (single 1 (.ref 0 : Shape (Payload Nat))) (.binder 0 (.ref 1)) =
        .binder 0 (.ref 0) := by simp [substitute, mask, single]
    rw [equal, self_binder_empty]
    simp [meaning]
  · rw [unused_binder _ 0 (.ref 1) (by simp [free])]
    simp [meaning, substitutedEnv, single]

end MicroCFTA.BinderLanguage
