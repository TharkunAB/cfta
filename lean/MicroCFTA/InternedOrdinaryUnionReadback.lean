import MicroCFTA.EqualityLeafProjectionPhysical
import MicroCFTA.InternedNormalizationFree

/-!
# Exact ordinary union reconstruction

Two distinct ordinary operands force the source ordinary merge branch.
Identity deduplication preserves the set of their complete resident rows.
The resulting node request has the same payload and cache effects as one
request over all original rows. Symbols and row arities can overlap.
The singleton union branch returns its operand without normalizing it.
-/
namespace MicroCFTA.InternedOrdinaryUnionReadback
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedUnionRetention InternedUnionSeparation
open InternedNodeSetCongruence EqualityLeafProjectionPhysical
open InternedBinderProtocol (Reference)

/-- An ordinary operand retains its actual complete node fields. -/
def Ordinary (value : Value Symbol Guard) : Prop :=
  ∃ entry edges depth free, value = .node entry edges depth free

/-- Ordinary operands contribute exactly one member each before deduplication. -/
theorem flatten_ordinary (values : List (Value Symbol Guard))
    (ordinary : ∀ value ∈ values, Ordinary value) : values.flatMap unionMembers = values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨entry, edges, depth, free, rfl⟩ := ordinary first List.mem_cons_self
      have tail := ih (fun value member => ordinary value (List.mem_cons_of_mem _ member))
      simp only [List.flatMap_cons, unionMembers, List.singleton_append, tail]

/-- The actual ordinary extractor concatenates the original ordered row payloads. -/
theorem ordinaryEdges_eq (values : List (Value Symbol Guard))
    (ordinary : ∀ value ∈ values, Ordinary value) :
    ordinaryEdges values = some (values.flatMap nodeEdges) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨entry, edges, depth, free, rfl⟩ := ordinary first List.mem_cons_self
      have tail := ih (fun value member => ordinary value (List.mem_cons_of_mem _ member))
      simp only [ordinaryEdges, tail, Option.map_some, List.flatMap_cons, nodeEdges]

/-- Every original row is resident in the actual edge table. -/
theorem rows_resident (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (linked : Linked state) (resident : ∀ value ∈ values, Resident state value) :
    ∀ edge ∈ values.flatMap nodeEdges, EdgeResident state edge := by
  intro edge member
  obtain ⟨value, included, selected⟩ := List.mem_flatMap.mp member
  exact resident_edges state linked value (resident value included) edge selected

/-- Identity deduplication changes no complete resident row membership. -/
theorem distinct_rows_member (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (resident : ∀ value ∈ values, Resident state value)
    (edge : EdgeValue Symbol Guard) :
    edge ∈ (distinctNodes values).flatMap nodeEdges ↔ edge ∈ values.flatMap nodeEdges := by
  constructor
  · rintro member
    obtain ⟨value, included, selected⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr ⟨value, distinctNodes_member values value included, selected⟩
  · rintro member
    obtain ⟨value, included, selected⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr
      ⟨value, distinctNodes_retains state coherent values resident value included, selected⟩

/-- The canonical ordinary request is unchanged by source operand deduplication. -/
theorem makeNode_distinct_rows (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value) :
    makeNode ((distinctNodes values).flatMap nodeEdges) = makeNode (values.flatMap nodeEdges) := by
  apply makeNode_same_members state coherent _ _
    (rows_resident _ state linked
      (fun value member => resident value (distinctNodes_member values value member)))
    (rows_resident values state linked resident)
  intro edge
  simp only [surviving, List.mem_filter, distinct_rows_member values state coherent resident edge]

/-- Two distinct original operands derive the actual ordinary merge computation. -/
theorem makeUnion_eq_makeNode [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (ordinary : ∀ value ∈ values, Ordinary value)
    (resident : ∀ value ∈ values, Resident state value)
    (left right : Value Symbol Guard) (leftMem : left ∈ values) (rightMem : right ∈ values)
    (different : left.referenceOf ≠ right.referenceOf) :
    run (makeUnion values) state = run (makeNode (values.flatMap nodeEdges)) state := by
  have flattened := flatten_ordinary values ordinary
  have retained := distinctNodes_retains state coherent values resident left leftMem
  have separated := separated_not_singleton values left right leftMem rightMem different
  have retainedOrdinary : ∀ value ∈ distinctNodes values, Ordinary value :=
    fun value member => ordinary value (distinctNodes_member values value member)
  have requests := makeNode_distinct_rows values state coherent linked resident
  cases normalized : distinctNodes values with
  | nil => simp only [normalized, List.not_mem_nil] at retained
  | cons first rest =>
      cases rest with
      | nil => exact False.elim (separated first normalized)
      | cons second tail =>
          have selected : ordinaryEdges (first :: second :: tail) =
              some ((first :: second :: tail).flatMap nodeEdges) :=
            ordinaryEdges_eq _ (by simpa only [normalized] using retainedOrdinary)
          simp only [makeUnion, flattened, normalized, selected]
          exact congrArg (fun request => run request state)
            (by simpa only [normalized] using requests)

/-- Actual union readback exposes every surviving original row and its canonical order. -/
theorem makeUnion_rows [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (ordinary : ∀ value ∈ values, Ordinary value)
    (resident : ∀ value ∈ values, Resident state value)
    (left right : Value Symbol Guard) (leftMem : left ∈ values) (rightMem : right ∈ values)
    (different : left.referenceOf ≠ right.referenceOf) :
    nodeEdges (run (makeUnion values) state).1 =
      canonicalEdges (surviving (values.flatMap nodeEdges)) := by
  rw [makeUnion_eq_makeNode values state coherent linked ordinary resident left right leftMem rightMem different]
  exact makeNode_edges _ state coherent linked (rows_resident values state linked resident)

/-- One live source row forces exact ordinary-node readback with computed metadata. -/
theorem makeNode_of_live_row [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (witness : ∃ edge ∈ edges, dead edge = false) :
    ∃ entry, (run (makeNode edges) state).1 =
      .node entry (canonicalEdges (surviving edges))
        (maximumDepth ((canonicalEdges (surviving edges)).flatMap EdgeValue.children))
        (childFree ((canonicalEdges (surviving edges)).flatMap EdgeValue.children)) := by
  obtain ⟨edge, included, live⟩ := witness
  have retained := (normalized_member state coherent edges resident edge).mpr ⟨included, live⟩
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  cases kept : canonicalEdges (surviving edges) with
  | nil => simp only [kept, List.not_mem_nil] at retained
  | cons first rest =>
      obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state coherent linked
        (by simpa only [kept] using selected)
      refine ⟨entry, ?_⟩
      simp only [makeNode, kept, run, readback, identifyNode]

/-- A nonempty free-name list with one possible name has its literal singleton form. -/
theorem canonicalFree_singleton (names : List Reference) (name : Reference)
    (present : name ∈ names) (only : ∀ other ∈ names, other = name) :
    canonicalFree names = [name] := by
  cases names with
  | nil => cases present
  | cons first rest =>
      have same := only first List.mem_cons_self
      subst first
      have removed : rest.filter (fun other => !(other == name)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other member
        simp [only other (List.mem_cons_of_mem name member)]
      rw [canonicalFree, List.eraseDups_cons, removed]
      simp only [List.eraseDups_nil, List.mergeSort_singleton]

/-- A live row with the designated name derives a depth-zero singleton-free node. -/
theorem makeNode_zero_singleton [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (name : Reference)
    (zero : ∀ child ∈ edges.flatMap EdgeValue.children, child.depth = 0)
    (only : ∀ child ∈ edges.flatMap EdgeValue.children, ∀ other ∈ child.free, other = name)
    (witness : ∃ edge ∈ edges, dead edge = false ∧
      ∃ child ∈ edge.children, name ∈ child.free) :
    ∃ entry, (run (makeNode edges) state).1 =
      .node entry (canonicalEdges (surviving edges)) 0 [name] := by
  let kept := canonicalEdges (surviving edges)
  have childOriginal : ∀ child ∈ kept.flatMap EdgeValue.children,
      child ∈ edges.flatMap EdgeValue.children := by
    intro child member
    obtain ⟨edge, included, selected⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr
      ⟨edge, (List.mem_filter.mp (canonicalEdges_member _ edge included)).1, selected⟩
  have exactDepth : maximumDepth (kept.flatMap EdgeValue.children) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (maximumDepth_exact _ 0).mpr
    intro child member
    exact Nat.le_of_eq (zero child (childOriginal child member))
  obtain ⟨edge, included, live, child, childMember, named⟩ := witness
  have keptEdge : edge ∈ kept :=
    (normalized_member state coherent edges resident edge).mpr ⟨included, live⟩
  have exactFree : childFree (kept.flatMap EdgeValue.children) = [name] := by
    apply canonicalFree_singleton _ name
    · exact List.mem_flatMap.mpr
        ⟨child, List.mem_flatMap.mpr ⟨edge, keptEdge, childMember⟩, named⟩
    · intro other member
      obtain ⟨value, selected, free⟩ := List.mem_flatMap.mp member
      exact only value (childOriginal value selected) other free
  obtain ⟨entry, readback⟩ := makeNode_of_live_row edges state coherent linked resident
    ⟨edge, included, live⟩
  refine ⟨entry, ?_⟩
  change (run (makeNode edges) state).1 = .node entry kept 0 [name]
  change (run (makeNode edges) state).1 =
    .node entry kept (maximumDepth (kept.flatMap EdgeValue.children))
      (childFree (kept.flatMap EdgeValue.children)) at readback
  rw [exactDepth, exactFree] at readback
  exact readback

end MicroCFTA.InternedOrdinaryUnionReadback
