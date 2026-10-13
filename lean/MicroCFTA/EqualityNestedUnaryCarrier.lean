import MicroCFTA.EqualityMergedTargetFixedPoint
import MicroCFTA.EqualityLeafProjectionProduct
import MicroCFTA.MergedColdMergeSoundness
import MicroCFTA.EqualityFixedProjectionTermination

/-!
# A generated carrier for nested unary equality endpoints

Each endpoint row has one child. That child has one nullary row with a
canonical admitted residual over at most two original outer guard atoms.
Source conjunction closes this carrier. Its generated inventory has at
most four rows, so the current target merger retains every root group.

The physical compiler proves exact merge replay for these nested endpoints.
The finite projected-row bound concerns the stated Cartesian row relation.
The complete physical intersection and endpoint-edit adapter is separate.
-/
namespace MicroCFTA.EqualityNestedUnaryCarrier
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityMergedTargetLayers EqualityMergedTargetFixedPoint EqualityMergedTargetReadback

abbrev Row := EqualityLeafProjectionAdmission.Row
abbrev ConstraintKey := EqualityLeafProjectionLeafCache.ConstraintKey

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- The finite nested row inventory is generated from the original outer guard atoms. -/
noncomputable def inventory (initial : List (Guard Formula)) : List (Row initial) :=
  EqualityLeafProjectionAdmission.inventory initial

/-- Source atom support of size at most two generates at most four nested row forms. -/
theorem inventory_bound (initial : List (Guard Formula)) (small : (SourceLeafRowProgress.basis initial).length ≤ 2) :
    (inventory initial).length ≤ 4 := by
  have bound := EqualityLeafProjectionAdmission.inventory_length initial
  have cases : (SourceLeafRowProgress.basis initial).length = 0 ∨
      (SourceLeafRowProgress.basis initial).length = 1 ∨ (SourceLeafRowProgress.basis initial).length = 2 := by omega
  rcases cases with zero | one | two
  · exact Nat.le_trans bound (by simp [zero])
  · exact Nat.le_trans bound (by simp [one])
  · exact Nat.le_trans bound (by simp [two])

/-- Every later nested row is one of the source-generated admitted residuals. -/
theorem inventory_complete (initial : List (Guard Formula)) (row : Row initial) : row ∈ inventory initial :=
  EqualityLeafProjectionAdmission.inventory_complete initial row

/-- Each unary row pairs two singleton children and uses actual source constraint conjunction there. -/
theorem child_constraint (initial : List (Guard Formula)) (left right : Row initial) :
    EqualityLeafProjectionProduct.combine (EqualityLeafProjectionLeafCache.constraint left)
      (EqualityLeafProjectionLeafCache.constraint right) =
      EqualityLeafProjectionLeafCache.constraint (EqualityLeafProjectionAdmission.join initial left right) := rfl

/-- The unconstrained unary parent retains Top when source intersection pairs two such rows. -/
theorem parent_constraint : EqualityLeafProjectionProduct.combine
    (some [], .top) (some [], .top) = (some [], .top) := by
  simp [EqualityLeafProjectionProduct.combine, SourceCompactGuards.combineEqualities,
    GuardConjunction.merge, GuardConjunction.normalize, GuardConjunction.atoms,
    GuardConjunction.canonical, GuardConjunction.conjoin]

/-- The exact set of selected complete nested rows. -/
abbrev Node (initial : List (Guard Formula)) := Row initial → Prop

/-- Enumerate a nested endpoint from its generated finite row inventory. -/
noncomputable def choices (node : Node initial) : List (Row initial) := by
  classical
  exact (inventory initial).filter (fun row => decide (node row))

/-- Every chosen row is selected, and every selected row occurs in the finite declaration list. -/
theorem choices_member (node : Node initial) (row : Row initial) : row ∈ choices node ↔ node row := by
  classical
  simp only [choices, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun member => ⟨inventory_complete initial row, member⟩⟩

/-- A complete nested endpoint cannot exceed the small-group threshold in this fragment. -/
theorem choices_bound (node : Node initial) (small : (SourceLeafRowProgress.basis initial).length ≤ 2) :
    (choices node).length ≤ 4 :=
  Nat.le_trans (List.length_filter_le _ _) (inventory_bound initial small)

/-- Node construction derives recursive exactness from at most four exact child rows. -/
theorem makeNode_exact [DecidableEq (EdgeKey Symbol Residual)] [DecidableEq Symbol]
    (edges : List (EdgeValue Symbol Residual)) (state : State Symbol Residual) (facts : Facts state) (prepared : Prepared state)
    (resident : Edges state edges) (small : edges.length ≤ 4)
    (childrenExact : ∀ edge ∈ edges, ∀ child ∈ edge.children, Normal Exact child) :
    Complete (fun _ => MergedColdMerge.work (makeNode edges)) state
      (fun after value => Available after value ∧ Normal Exact value) := by
  have verified := node_verified edges state facts resident
  let result := run (makeNode edges) state
  have resultFacts : Facts result.2 := verified.facts
  have available : Available result.2 result.1 := verified.result _ _ rfl
  have readback := EqualityOrdinaryReadback.makeNode_normal edges state result.2 facts.coherent facts.linked
    resultFacts.coherent resident (grows_refl _)
  have rootExact : Exact result.1 := by
    constructor
    · intro entry rows depth same key
      have bound := MergedNodeRowBounds.makeNode_key_bound edges state facts.coherent facts.linked resident key 4
        (Nat.le_trans (List.length_filter_le _ _) small)
      simpa only [result, same, nodeEdges] using bound
    · intro entry rows depth same
      exact ⟨result.2, resultFacts, available, readback⟩
  have normal : Normal Exact result.1 := by
    apply Normal.intro rootExact
    intro child member
    have output : child ∈ (nodeEdges result.1).flatMap EdgeValue.children := by
      generalize valueEq : result.1 = value at member ⊢
      cases value <;> simp_all [EqualityMergedTargetLayers.children, nodeEdges]
    obtain ⟨edge, present, included⟩ := List.mem_flatMap.mp output
    rw [EqualityLeafProjectionPhysical.makeNode_edges edges state facts.coherent facts.linked resident] at present
    exact childrenExact edge (List.mem_filter.mp (canonicalEdges_member _ edge present)).1 child included
  exact MergedColdMergeSoundness.work_post _ state prepared Available _ verified (makeNode_noNewMu _ _) ⟨available, normal⟩

/-- Build an actual unary edge over one actual nullary child with the complete source constraints. -/
noncomputable def rowAction [DecidableEq Symbol] (parent leaf : Symbol) (row : Row initial) :
    Action Symbol ConstraintKey (EdgeValue Symbol ConstraintKey) :=
  MergedColdMerge.bind (MergedColdMerge.work (makeEdge leaf (EqualityLeafProjectionLeafCache.constraint row) [])) fun edge =>
    MergedColdMerge.bind (MergedColdMerge.work (makeNode [edge])) fun child =>
      MergedColdMerge.work (makeEdge parent (some [], .top) [child])

/-- A returned parent edge retains residency and exact constructor replay for each child. -/
def EdgePost [DecidableEq (EdgeKey Symbol Residual)] [DecidableEq Symbol]
    (state : State Symbol Residual) (edge : EdgeValue Symbol Residual) : Prop :=
  EdgeResident state edge ∧ ∀ child ∈ edge.children, Normal Exact child

/-- Unary row construction derives exact child replay without a callback premise. -/
theorem row_complete [DecidableEq Symbol] (parent leaf : Symbol) (row : Row initial)
    (state : State Symbol ConstraintKey) (facts : Facts state) (prepared : Prepared state) :
    Complete (fun _ => rowAction parent leaf row) state EdgePost := by
  have verified := edge_verified leaf (EqualityLeafProjectionLeafCache.constraint row) [] state facts (by simp)
  apply bind_complete _ _ state (fun after edge => EdgeResident after edge ∧ edge.children = []) _
    (MergedColdMergeSoundness.work_post _ state prepared EdgeResident _ verified
      (by intro key entry body depth ordinary stored; exact stored)
      ⟨verified.result _ _ rfl, InternedShallowValues.makeEdge_children _ _ [] state facts.coherent facts.cached (by simp)⟩)
  intro edge middle firstExtension edgePost
  apply bind_complete _ _ middle _ _ (makeNode_exact [edge] middle firstExtension.facts firstExtension.prepared
    (by intro value member; simpa only [List.mem_singleton.mp member] using edgePost.1) (by simp)
    (by intro value member child included; rw [List.mem_singleton.mp member, edgePost.2] at included; contradiction))
  intro child after secondExtension childPost
  have children : Values after [child] := by intro value member; simpa only [List.mem_singleton.mp member] using childPost.1
  have verified := edge_verified parent (some [], .top) [child] after secondExtension.facts children
  apply MergedColdMergeSoundness.work_post _ after secondExtension.prepared EdgeResident _ verified
    (by intro key entry body depth ordinary stored; exact stored)
  refine ⟨verified.result _ _ rfl, ?_⟩
  rw [InternedShallowValues.makeEdge_children parent (some [], .top) [child] after secondExtension.facts.coherent secondExtension.facts.cached children]
  intro value member
  simpa only [List.mem_singleton.mp member] using childPost.2

/-- Compile selected nested alternatives with the actual ordered edge and node requests. -/
noncomputable def compile [DecidableEq Symbol] (parent leaf : Symbol) (node : Node initial) :
    Action Symbol ConstraintKey (Value Symbol ConstraintKey) :=
  MergedColdMerge.bind (MergedColdMerge.map (rowAction parent leaf) (choices node)) (fun edges => MergedColdMerge.work (makeNode edges))

/-- Every compiled nested endpoint derives exact recursive replay from its generated source inventory. -/
theorem compile_complete [DecidableEq Symbol] (parent leaf : Symbol) (node : Node initial)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (state : State Symbol ConstraintKey) (facts : Facts state) (prepared : Prepared state) :
    Complete (fun _ => compile parent leaf node) state
      (fun after value => Available after value ∧ Normal Exact value) := by
  have rows := MergedColdMergeSoundness.map_related (fun _ => rowAction parent leaf)
    (fun _ _ => True) (fun state _ edge => EdgePost state edge)
    (fun _ _ _ _ _ => trivial)
    (fun before after extension _ edge post => ⟨edge_grows before after extension.growth edge post.1, post.2⟩)
    (choices node) (fun row _ before facts prepared _ => row_complete parent leaf row before facts prepared)
    state facts prepared (by simp)
  apply bind_complete _ _ state _ _ rows
  intro edges after extension related
  have all := EnumerationSoundness.all₂_outputs _ _ _ related
  exact makeNode_exact edges after extension.facts extension.prepared
    (fun edge member => (all edge member).1)
    (by rw [← related.length_eq]; exact choices_bound node small)
    (fun edge member => (all edge member).2)

/-- The actual current-policy target merger returns each compiled nested endpoint and cache unchanged. -/
theorem compile_merge_fixed [DecidableEq Symbol] (parent leaf : Symbol) (node : Node initial)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (state : State Symbol ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (clear : ConstraintKey → Bool) :
    ∃ value after, compile parent leaf node state = .done value after ∧
      Extension state after ∧ Available after value ∧
      ∀ comparison, execute MergedSourceGrouping.groups clear (some [], .top) comparison value after = .done value after := by
  obtain ⟨bound, value, after, done, extension, available, normal⟩ := compile_complete parent leaf node small state facts prepared
  exact ⟨value, after, done bound (Nat.le_refl _), extension, available,
    fun comparison => execute_fixed clear (some [], .top) comparison value normal after extension.facts extension.prepared available⟩

/-- The nested Cartesian row relation is the actual canonical conjunction of its singleton child guards. -/
def Join (initial : List (Guard Formula)) (left right result : Row initial) : Prop :=
  EqualityLeafProjectionAdmission.join initial left right = result

/-- Canonical source conjunction supplies every admitted diagonal nested row. -/
theorem join_diagonal (initial : List (Guard Formula)) (row : Row initial) : Join initial row row row :=
  (EqualityLeafProjectionAdmission.algebra initial).idem row

/-- Source operand ordering does not change the generated nested row. -/
theorem join_symmetric (initial : List (Guard Formula)) (left right result : Row initial) :
    Join initial left right result ↔ Join initial right left result := by
  unfold Join
  have same : EqualityLeafProjectionAdmission.join initial left right = EqualityLeafProjectionAdmission.join initial right left :=
    (EqualityLeafProjectionAdmission.algebra initial).comm left right
  rw [same]

/-- Original unary ancestor occurrences retain distinct positions on each side of the projected class. -/
abbrev Projected (initial : List (Guard Formula)) (left right : Nat) :=
  EqualityFixedProjectionTermination.State (Fin left) (Fin right) (Row initial)

/-- Generate every original occurrence index without a supplied finite-universe premise. -/
def positions (left right : Nat) : List (Sum (Fin left) (Fin right)) :=
  (List.finRange left).map Sum.inl ++ (List.finRange right).map Sum.inr

/-- Original occurrences and generated residuals give the complete nested row-state inventory. -/
noncomputable def entries (initial : List (Guard Formula)) (left right : Nat) :
    List (Sum (Fin left) (Fin right) × Row initial) :=
  (positions left right).flatMap fun position => (inventory initial).map (position, ·)

/-- Every indexed nested row belongs to the generated inventory. -/
theorem entries_complete (initial : List (Guard Formula)) (left right : Nat)
    (entry : Sum (Fin left) (Fin right) × Row initial) : entry ∈ entries initial left right := by
  obtain ⟨position, row⟩ := entry
  apply List.mem_flatMap.mpr
  refine ⟨position, ?_, List.mem_map.mpr ⟨row, inventory_complete initial row, rfl⟩⟩
  cases position <;> simp [positions]

/-- At most four generated nested rows occur at each original occurrence position. -/
theorem entries_bound (initial : List (Guard Formula)) (left right : Nat)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2) :
    (entries initial left right).length ≤ 4 * (left + right) := by
  have length : ∀ positions : List (Sum (Fin left) (Fin right)),
      (positions.flatMap fun position => (inventory initial).map (position, ·)).length =
        positions.length * (inventory initial).length := by
    intro values
    induction values with
    | nil => simp
    | cons first rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
  rw [entries, length]
  have count : (positions left right).length = left + right := by simp [positions]
  rw [count]
  have bound := Nat.mul_le_mul_left (left + right) (inventory_bound initial small)
  simpa only [Nat.mul_comm] using bound

/-- The concrete nested row relation derives the post-first-pass strict finite progress measure. -/
theorem projected_strict (initial : List (Guard Formula)) (left right : Nat)
    (state : Projected initial left right)
    (changed : EqualityFixedProjectionTermination.step (Join initial)
      (EqualityFixedProjectionTermination.step (Join initial) state) ≠
      EqualityFixedProjectionTermination.step (Join initial) state) :
    EqualityFixedProjectionTermination.potential (entries initial left right)
        (EqualityFixedProjectionTermination.step (Join initial) (EqualityFixedProjectionTermination.step (Join initial) state)) <
      EqualityFixedProjectionTermination.potential (entries initial left right)
        (EqualityFixedProjectionTermination.step (Join initial) state) :=
  EqualityFixedProjectionTermination.after_first_strict (Join initial) (join_diagonal initial) (join_symmetric initial)
    (entries initial left right) (entries_complete initial left right) state changed

/-- The generated nested row schedule reaches its identity fixed point within four slots per occurrence plus two tests. -/
theorem projected_bound (initial : List (Guard Formula)) (left right : Nat)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2) (state : Projected initial left right) :
    ∃ fuel result, fuel ≤ 4 * (left + right) + 2 ∧
      EqualityFixedProjectionTermination.run (Join initial) fuel state = some result ∧
      EqualityFixedProjectionTermination.step (Join initial) result = result := by
  obtain ⟨result, done, fixed⟩ := EqualityFixedProjectionTermination.run_bounded (Join initial)
    (join_diagonal initial) (join_symmetric initial) (entries initial left right) (entries_complete initial left right) state
  refine ⟨_, result, ?_, done, fixed⟩
  have bound := entries_bound initial left right small
  have remaining := Nat.sub_le (entries initial left right).length
    (FiniteRowIntersection.count (entries initial left right)
      (EqualityFixedProjectionTermination.member (EqualityFixedProjectionTermination.step (Join initial) state)))
  change (entries initial left right).length - _ + 2 ≤ _
  omega

end MicroCFTA.EqualityNestedUnaryCarrier
