import MicroCFTA.SourceCurrentConstrainedCapRequiredSupport

/-!
# Uniform finite caps and all supported paths

A cap bound is equivalent to support at every path of that length.
The path relation can therefore retain a cap through actual replacements.
Missing signed positions remain vacuous. Mu requires a hereditary body.
These are syntax laws. They do not assert native or outer completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMaskCharacterization
open InternedConstructorTemplates SourceEqualityAnnotationLanguage
open SourceEqualityProjectionGraph
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPaths (Supported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
variable {Symbol Guard : Type}

/-- Support at every exact-depth path bounds all constrained ordinary layers. -/
theorem of_uniform (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (supported : ∀ path : List Int, path.length = depth → Supported valid path value) : Cap valid depth value := by
  induction depth generalizing value with
  | zero => exact .plain 0 (supported [] rfl).root
  | succ depth depthIH =>
      have lift : ∀ (path : List Int) (input : Value Symbol Guard), Supported valid path input →
          (∀ path : List Int, path.length = depth + 1 → Supported valid path input) → Cap valid (depth + 1) input := by
        intro path input witness
        induction witness with
        | plain path annotated =>
            intro _
            exact .plain (depth + 1) annotated
        | node index path entry edges level free children _ih =>
            intro masks
            apply Cap.node depth entry edges level free
            intro child member
            obtain ⟨edge, edgeMember, childMember⟩ := List.mem_flatMap.mp member
            obtain ⟨slot, found⟩ := List.getElem?_of_mem childMember
            have nonnegative : ¬ (slot : Int) < 0 := by omega
            have selected : select edge.children (slot : Int) = some child := by
              simpa only [select, nonnegative, ↓reduceIte, Int.toNat_natCast] using found
            apply depthIH child
            intro suffix length
            exact (masks ((slot : Int) :: suffix) (by simp only [List.length_cons, length])).node_selected edge edgeMember child selected
        | union path entry members level free children ih =>
            intro masks
            apply Cap.union (depth + 1) entry members level free
            intro child member
            exact ih child member (fun path length => (masks path length).union_member child member)
      exact lift (List.replicate (depth + 1) (0 : Int)) value
        (supported _ (List.length_replicate ..)) supported

/-- The uniform cap and exact-depth positional conditions describe the same finite syntax. -/
theorem cap_iff_uniform (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard) :
    Cap valid depth value ↔ ∀ path : List Int, path.length = depth → Supported valid path value := by
  constructor
  · intro cap path length
    exact SourceCurrentConstrainedCapPaths.of_cap cap path (by omega)
  · exact of_uniform valid depth value

/-- Retaining every original path also retains each original uniform cap bound. -/
theorem preserves_cap {valid : Guard → Prop} {depth : Nat} {original result : Value Symbol Guard}
    (preserved : Preserves valid original result) (bounded : Cap valid depth original) : Cap valid depth result := by
  apply of_uniform valid depth result
  intro path length
  exact preserved path (SourceCurrentConstrainedCapPaths.of_cap bounded path (by omega))

/-- An ordered all-path relation retains the cap on every original child slot. -/
theorem children_cap {valid : Guard → Prop} {depth : Nat} {originals results : List (Value Symbol Guard)}
    (related : Language.All₂ (Preserves valid) originals results)
    (bounded : ∀ value ∈ originals, Cap valid depth value) : ∀ value ∈ results, Cap valid depth value := by
  induction related with
  | nil => intro value member; cases member
  | cons first rest ih =>
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact preserves_cap first (bounded _ List.mem_cons_self)
      · exact ih (fun value present => bounded value (List.mem_cons_of_mem _ present)) value member

end MicroCFTA.SourceCurrentConstrainedCapMaskCharacterization
