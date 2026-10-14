import MicroCFTA.SourceRecursiveIntersectionKernelCalls

/-!
# Verified full recursive intersection caller

Every source branch composes the actual domain and constructor effects.
All bounded calls retain complete cache facts and both histories. Every
successful result is an available source value. Open calls can return
recursive placeholders. This theorem
does not assert that all bounds succeed or establish product language.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain

/-- Ordered source union requests retain available results before union construction. -/
theorem union_checked [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (members : List (Value Symbol Guard)) (other : Value Symbol Guard)
    (left : Bool) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value) :
    Checked state
      ((walk (fun member => if left then call domain member other else call domain other member) members state).bind
        fun values after => work (makeUnion values) after)
      (fun after value => Available after.heap value) := by
  let input := fun (state : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap other ∧ Available state.heap value
  have stable : Stable input := by
    intro before after extension value known
    exact ⟨known.1.grows domain extension, extension.available _ known.2.1, extension.available _ known.2.2⟩
  have requests := walk_checked
    (fun member => if left then call domain member other else call domain other member) members input _ stable available_stable
    (by
      intro member _ current currentValid known
      cases left
      · exact calls domain other member current currentValid known.1 known.2.1 known.2.2
      · exact calls domain member other current currentValid known.1 known.2.2 known.2.1)
    state valid (fun member present => ⟨known, available, membersAvailable member present⟩)
  apply checked_bind state _ _ _ _ requests
  intro values after returned afterValid available
  exact work_checked after afterValid _ Available (InternedNestedFacts.union_verified values after.heap afterValid.1 available)

/-- Full source branch selection composes checked recursive requests with exact physical effects. -/
theorem onNode_checked [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : Valid state) (known : Domain state domain) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) :
    Checked state (onNode emptyGuard conjoin call domain left right state) (fun after value => Available after.heap value) := by
  cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
  | empty =>
      simp only [onNode, selected]
      exact checked_pure state valid (Value.empty (Symbol := Symbol) (Guard := Guard)) _ (empty_available state.heap)
  | reset =>
      simp only [onNode, selected]
      exact calls _ left right state valid (empty_domain state) leftAvailable rightAvailable
  | self =>
      simp only [onNode, selected]
      exact checked_pure state valid left _ leftAvailable
  | swap =>
      simp only [onNode, selected]
      exact calls domain right left state valid known rightAvailable leftAvailable
  | repeated key =>
      simp only [onNode, selected]
      apply checked_pure state valid _ _
      apply reference_available state.heap (.intersection key.1 key.2)
      intro name member
      simp [Value.free] at member
  | bothMu | leftMu | rightMu =>
      simp only [onNode, selected]
      exact mu_checked call calls domain left right state valid known leftAvailable rightAvailable
  | leftUnion =>
      simp only [onNode, selected]
      cases left with
      | union entry members depth free =>
          exact union_checked call calls domain members right true state valid known rightAvailable
            (fun value member => leftAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => exact unsupported_checked _ _ state valid
  | rightUnion =>
      simp only [onNode, selected]
      cases right with
      | union entry members depth free =>
          exact union_checked call calls domain members left false state valid known leftAvailable
            (fun value member => rightAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => exact unsupported_checked _ _ state valid
  | leftReference =>
      simp only [onNode, selected]
      cases left with
      | reference name =>
          cases name <;> try exact unsupported_checked _ _ state valid
          rename_i identity
          exact reference_checked call calls domain identity right true state valid known rightAvailable
      | empty | node | union | mu => exact unsupported_checked _ _ state valid
  | rightReference =>
      simp only [onNode, selected]
      cases right with
      | reference name =>
          cases name <;> try exact unsupported_checked _ _ state valid
          rename_i identity
          exact reference_checked call calls domain identity left false state valid known leftAvailable
      | empty | node | union | mu => exact unsupported_checked _ _ state valid
  | ordinary =>
      simp only [onNode, selected]
      cases left <;> cases right <;> try exact unsupported_checked _ _ state valid
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact node_checked emptyGuard conjoin call calls domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
  | unsupported =>
      simp only [onNode, selected]
      exact unsupported_checked _ _ state valid

/-- Every bounded recursive source call derives complete state invariants and available successful results. -/
theorem execute_checked [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) : Calls (execute (Symbol := Symbol) emptyGuard conjoin fuel) := by
  induction fuel with
  | zero =>
      intro domain left right state valid known leftAvailable rightAvailable
      simp only [execute]
      exact checked_failed state valid .exhausted _
  | succ fuel ih =>
      intro domain left right state valid known leftAvailable rightAvailable
      simp only [execute]
      exact onNode_checked emptyGuard conjoin _ ih domain left right state valid known leftAvailable rightAvailable

end MicroCFTA.SourceRecursiveIntersectionKernel
