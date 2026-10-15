import MicroCFTA.SourceMergedEdgeCompletion

/-!
# Stable finite general repaired merging

Finite ordered groups combine the general comparison bounds. Ordinary
height derives every recursive merge call. All closed available inputs
have stable finite execution with their actual complete returned caches.
-/
namespace MicroCFTA.SourceMergedCompletion
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedColdMerge (Action pure)
open MergedOrdinaryHeight
open SourceMergedCompleteEffects SourceMergedColumnCompletion SourceMergedEdgeCompletion
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Both source group branches have stable finite execution with closed resident row results. -/
theorem group_complete (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (top : Guard)
    (smaller : ∀ value, height value ≤ limit → ∀ before, SemanticReady before → Available before value → value.free = [] →
      Complete (fun fuel => recurse fuel value) before ValueReady)
    (edges : List (EdgeValue Symbol Guard)) (bounded : ∀ edge ∈ edges, ∀ value ∈ edge.children, height value ≤ limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (ready : ∀ edge ∈ edges, EdgeReady before edge) :
    Complete (fun fuel => SourceMergedWorker.group (recurse fuel) clear fuel top edges) before
      (fun after results => ∀ edge ∈ results, EdgeReady after edge) := by
  by_cases smallGroup : edges.length ≤ 4
  · simp only [SourceMergedWorker.group, smallGroup, ite_true]
    exact map_complete (fun fuel => MergedColdMerge.small (recurse fuel)) EdgeReady EdgeReady edge_grows edge_grows edges
      (fun edge member state semantic input => small_complete recurse limit smaller edge (bounded edge member) state semantic input)
      before semantic ready
  · cases edges with
    | nil => simp at smallGroup
    | cons first rest =>
        simp only [SourceMergedWorker.group, smallGroup, ite_false]
        apply bind_complete _ _ before EdgeReady _ (large_complete recurse limit clear top smaller first rest bounded before semantic ready)
        intro value after effects available
        exact pure_complete [value] after effects.2 _ (by
          intro edge member
          simpa only [List.mem_singleton.mp member] using available)

/-- Complete structural grouping combines every source row before the actual final node. -/
theorem root_complete (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (top : Guard)
    (smaller : ∀ value, height value ≤ limit → ∀ before, SemanticReady before → Available before value → value.free = [] →
      Complete (fun fuel => recurse fuel value) before ValueReady)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (groups : List (List (EdgeValue Symbol Guard))) (grouping : MergedPhysicalGroupRoot.Grouping edges groups)
    (heightBound : height (.node entry edges depth []) ≤ limit + 1)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before (.node entry edges depth [])) :
    Complete (fun fuel => SourceMergedWorker.root (recurse fuel) clear fuel top groups) before ValueReady := by
  have original : ∀ group ∈ groups, ∀ edge ∈ group, edge ∈ edges := by
    intro group member edge included
    exact grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have rows := map_complete (fun fuel => SourceMergedWorker.group (recurse fuel) clear fuel top)
    (fun state edges => ∀ edge ∈ edges, EdgeReady state edge) (fun state edges => ∀ edge ∈ edges, EdgeReady state edge)
    (fun before after effects _ ready edge member => edge_grows before after effects edge (ready edge member))
    (fun before after effects _ ready edge member => edge_grows before after effects edge (ready edge member)) groups
    (fun group member state semantic ready => group_complete recurse limit clear top smaller group
      (fun edge included value inner => by
        have less := child_lt entry edges depth [] edge (original group member edge included) value inner
        omega) state semantic ready)
    before semantic (fun group member edge included => ⟨InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
      _ available.resident edge (original group member edge included),
      fun child inner => closed_child before semantic.ready.semantic.1.normal.facts.coherent entry edges depth [] available.resident rfl
        edge (original group member edge included) child inner⟩)
  apply bind_complete _ _ before _ ValueReady rows
  intro groups after effects ready
  exact node_complete groups.flatten after effects.2 (by
    intro edge member
    obtain ⟨group, included, member⟩ := List.mem_flatten.mp member
    exact ready group included edge member)

/-- Ordinary height derives complete general repaired merging without supplied recursive or comparison laws. -/
theorem worker_complete (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinaryFuel : Nat) (value : Value Symbol Guard) (enough : height value ≤ ordinaryFuel)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    Complete (fun fuel => SourceMergedWorker.worker grouping clear top ordinaryFuel fuel value) before ValueReady := by
  induction ordinaryFuel generalizing value before with
  | zero =>
      cases value with
      | empty | reference | union | mu => exact pure_complete _ before semantic ValueReady ⟨available, closed⟩
      | node => simp [height] at enough
  | succ ordinaryFuel ih =>
      cases value with
      | empty | reference | union | mu => exact pure_complete _ before semantic ValueReady ⟨available, closed⟩
      | node entry edges depth free =>
          have freeEmpty : free = [] := closed
          subst free
          simpa only [SourceMergedWorker.worker, ite_true] using root_complete
            (fun fuel => SourceMergedWorker.worker grouping clear top ordinaryFuel fuel) ordinaryFuel clear top
            (fun value bound state semantic available closed => ih value bound state semantic available closed)
            entry edges depth (grouping edges) (groupsCorrect edges) enough before semantic available

/-- Executable source grouping and the original ordinary height give one stable finite comparison bound. -/
theorem execute_complete (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    Complete (fun fuel => SourceMergedWorker.execute clear top fuel value) before ValueReady :=
  worker_complete MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top (height value) value (Nat.le_refl _)
    before semantic available closed

end MicroCFTA.SourceMergedCompletion
