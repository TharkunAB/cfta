import MicroCFTA.MergedFreshOrdinaryExposureCoverage

/-!
# Exact epsilon-origin equations for repaired physical records

Origins retain complete physical edge records. Seed lists are exact unions.
Union and completed Mu steps expose their actual repaired successors.
These equations do not replace a Mu or union by its ordinary row projection.
-/
namespace MicroCFTA.MergedFreshOrdinaryGraph
open Cache InternedConstructorTemplates InternedEdgeResidency
open InternedBinderProtocol Productivity

/-- Every constructor origin comes from one original seed occurrence. -/
theorem origin_seeds [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (edge : EdgeValue Symbol Guard) :
    Origin view roots edge ↔ ∃ root ∈ roots, Origin view [root] edge := by
  constructor
  · rintro ⟨source, reached, member⟩
    have start : ∃ root ∈ roots, Reachable (successors view) [root] source := by
      clear member
      induction reached with
      | seed present => exact ⟨_, present, .seed List.mem_cons_self⟩
      | step prior next ih =>
          obtain ⟨root, present, path⟩ := ih
          exact ⟨root, present, .step path next⟩
    obtain ⟨root, present, path⟩ := start
    exact ⟨root, present, source, path, member⟩
  · rintro ⟨root, present, origin⟩
    apply origin.from_seeds view [root] roots _ edge
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact .seed present

/-- A record with no ordinary rows delegates its origins to its exact epsilon successors. -/
theorem origin_expand [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (root : Value Symbol Guard) (noEdges : nodeEdges root = []) (edge : EdgeValue Symbol Guard) :
    Origin view [root] edge ↔ Origin view (successors view root) edge := by
  constructor
  · rintro ⟨source, reached, member⟩
    have split : source = root ∨ Reachable (successors view) (successors view root) source := by
      clear member
      induction reached with
      | seed present => exact Or.inl (List.mem_singleton.mp present)
      | step prior next ih =>
          rcases ih with rfl | path
          · exact Or.inr (.seed next)
          · exact Or.inr (.step path next)
    rcases split with rfl | path
    · simp only [noEdges, List.not_mem_nil] at member
    · exact ⟨source, path, member⟩
  · intro origin
    apply origin.from_seeds view (successors view root) [root] _ edge
    intro value member
    exact .step (.seed List.mem_cons_self) member

/-- EmptyNode has no constructor origin. -/
theorem origin_empty [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard) (edge : EdgeValue Symbol Guard) :
    ¬ Origin view [.empty] edge := by
  intro origin
  have member := MergedFreshOrdinaryExposureCoverage.origin_terminal view .empty rfl edge origin
  cases member

/-- An ordinary record exposes exactly its complete literal rows. -/
theorem origin_node [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (edge : EdgeValue Symbol Guard) :
    Origin view [.node entry edges depth free] edge ↔ edge ∈ edges := by
  constructor
  · exact MergedFreshOrdinaryExposureCoverage.origin_terminal view _ rfl edge
  · intro member
    exact ⟨_, .seed List.mem_cons_self, member⟩

/-- A stored union exposes exactly the origins of its actual members. -/
theorem origin_union [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (edge : EdgeValue Symbol Guard) :
    Origin view [.union entry members depth free] edge ↔ ∃ member ∈ members, Origin view [member] edge := by
  rw [origin_expand view _ rfl]
  exact origin_seeds view members edge

/-- Actual completed repaired Mu unfolding preserves every complete edge origin. -/
theorem origin_unfold [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary result : Value Symbol Guard)
    (after : State Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) view = .done result after)
    (edge : EdgeValue Symbol Guard) :
    Origin view [.mu entry body depth ordinary] edge ↔ Origin view [result] edge := by
  rw [origin_expand view _ rfl]
  simp only [successors, done]

end MicroCFTA.MergedFreshOrdinaryGraph
