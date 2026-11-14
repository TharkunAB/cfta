import MicroCFTA.SourceSynthesisUniverseOrigins
import MicroCFTA.SourceSynthesisCurrentConstruction

/-!
# Current source prefix over its computed universe

The current source context uses its computed constructor catalog.
Every successful source expression has an ordinary prefix over that universe.
The expression need not contain the universe. This law does not identify a
native universe value or assert native completion.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseOrigins
open SourceSynthesisTypeSyntax (Library Query allTypes)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseOrigins

set_option autoImplicit false

private theorem context_closed (lib : Library) (query : Query) :
    ContextClosed (OverUniverse (SourceSynthesisCurrentContext.context lib query).types)
      (SourceSynthesisCurrentContext.context lib query) := by
  refine ⟨.atom, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    intro child inside
    have same := List.mem_singleton.mp inside
    subst child
    exact generalize_overUniverse _ _
  · intro entry member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    intro child inside
    have same := List.mem_singleton.mp inside
    subst child
    exact typeNode_overUniverse _ _
  · apply OverUniverse.node
    intro row member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    intro child inside
    have same := List.mem_singleton.mp inside
    subst child
    exact generalize_overUniverse _ _

private theorem bind_ok {Error Input Output : Type} (action : Except Error Input)
    (next : Input → Except Error Output) (value : Output)
    (returned : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases returned
  | ok input => exact ⟨input, rfl, returned⟩

private theorem mapM_preserves {Error Input Output : Type} (P : Output → Prop)
    (action : Input → Except Error Output) (inputs : List Input) (outputs : List Output)
    (checked : ∀ input output, action input = .ok output → P output)
    (returned : inputs.mapM action = .ok outputs) : ∀ output ∈ outputs, P output := by
  have related := SymbolicDriver.mapM_success_all₂ action inputs outputs returned
  have certificates := related.imp (fun input output success =>
    iff_of_true True.intro (checked input output success))
  exact (SymbolicDriver.all₂_forall_iff (fun _ => True) P inputs outputs certificates).mp (by simp)

/-- A successful current source expression uses only its computed universe binder. -/
theorem firstOrderRaw_overUniverse (lib : Library) (query : Query) (signed : Int)
    (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression) :
    OverUniverse (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)) expression := by
  have closed : Closed (OverUniverse
      (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))) :=
    ⟨OverUniverse.node, OverUniverse.union⟩
  unfold SourceSynthesisCurrentConstruction.firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    apply OverUniverse.node
    intro row member
    have same := List.mem_singleton.mp member
    subst row
    intro child inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact typeNode_overUniverse _ _
    · apply OverUniverse.union
      intro row member
      obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
      have chunksP : ∀ chunk ∈ chunks, ∀ row ∈ chunk,
          OverUniverse (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)) row := by
        apply mapM_preserves (fun chunk => ∀ row ∈ chunk,
          OverUniverse (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)) row)
          _ _ _ _ chunksResult
        intro arguments rows result
        exact relevantRows_induction _ closed _ (context_closed lib query)
          signed.toNat true _ rows result
      exact chunksP chunk included row inside


end MicroCFTA.SourceSynthesisCurrentUniverseOrigins
