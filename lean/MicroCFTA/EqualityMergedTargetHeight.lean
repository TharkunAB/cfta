import MicroCFTA.EqualityMergedTargetShape

/-!
# Ordinary height after an actual target merge

This proof covers finite ordinary input trees. It excludes references,
Mu records, and explicit union records. The actual worker preserves this
fragment and cannot increase its ordinary height. The ordered selection
and constructor effects remain in the execution trace.
-/
namespace MicroCFTA.EqualityMergedTargetHeight
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedColdMergeMapFacts
open MergedOrdinaryHeight Language

/-- Finite ordinary trees stop only at empty values and contain no recursive or union records. -/
inductive Tree : Value Symbol Guard → Prop where
  | empty : Tree .empty
  | node (entry) (edges : List (EdgeValue Symbol Guard)) (depth free)
      (children : ∀ edge ∈ edges, ∀ child ∈ edge.children, Tree child) : Tree (.node entry edges depth free)

/-- Ordinary-tree roots never enter the recursive-union column branch. -/
theorem tree_boundary (value : Value Symbol Guard) (tree : Tree value) : recursiveBoundary value = false := by
  cases tree <;> rfl

/-- Every outgoing child of an ordinary tree is an ordinary tree. -/
theorem tree_child (value : Value Symbol Guard) (tree : Tree value) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ nodeEdges value) (child : Value Symbol Guard) (included : child ∈ edge.children) : Tree child := by
  cases tree with
  | empty => contradiction
  | node entry edges depth free children => exact children edge member child included

/-- Canonical ordinary node readback retains the ordinary-tree fragment. -/
theorem makeNode_tree [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : Edges state edges)
    (trees : ∀ edge ∈ edges, ∀ child ∈ edge.children, Tree child) : Tree (run (makeNode edges) state).1 := by
  have selected : Edges state (canonicalEdges (surviving edges)) :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedTrees : ∀ edge ∈ canonicalEdges (surviving edges), ∀ child ∈ edge.children, Tree child :=
    fun edge member => trees edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa only [same, Edges] using selected)
    simp only [run, exactResult, identifyNode]
    exact .node _ _ _ _ (by simpa only [same] using selectedTrees)

/-- Ordinary column union preserves the input fragment before its recursive merge call. -/
theorem ordinaryUnion_tree [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (available : Values state values)
    (trees : ∀ value ∈ values, Tree value) : Tree (run (ordinaryUnion values) state).1 := by
  apply makeNode_tree _ state facts
  · intro edge member
    obtain ⟨value, included, inner⟩ := List.mem_flatMap.mp member
    exact resident_edges state facts.linked value (available value included).resident edge inner
  · intro edge member child included
    obtain ⟨value, present, inner⟩ := List.mem_flatMap.mp member
    exact tree_child value (trees value present) edge inner child included

/-- A recursive call preserves the finite ordinary fragment and its input height. -/
def HeightCall (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ input before result after, Facts before → Prepared before → Available before input → Tree input →
    call input before = .done result after → Tree result ∧ height result ≤ height input

/-- A bounded returned ordinary value retains its actual cache availability. -/
def Bounded (limit : Nat) (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  Available state value ∧ Tree value ∧ height value ≤ limit

/-- Cache extensions preserve ordinary shape and height because complete values are immutable. -/
theorem bounded_grows (limit : Nat) (before after : State Symbol Guard) (extension : Extension before after)
    (value : Value Symbol Guard) (bounded : Bounded limit before value) : Bounded limit after value :=
  ⟨extension.available value bounded.1, bounded.2⟩

/-- Ordered recursive calls preserve a common height bound on their actual output list. -/
theorem map_bounded (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (nonincrease : HeightCall call) (limit : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ input ∈ inputs, Bounded limit before input)
    (outputs : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : MergedColdMerge.map call inputs before = .done outputs after) :
    Extension before after ∧ ∀ output ∈ outputs, Bounded limit after output := by
  obtain ⟨extension, related⟩ := map_valid call (Bounded limit) (fun state _ result => Bounded limit state result)
    (bounded_grows limit) (fun before after extension _ result bounded => bounded_grows limit before after extension result bounded)
    (fun input before result after facts prepared bounded done => by
      obtain ⟨extension, available⟩ := checked input before result after facts prepared bounded.1 done
      obtain ⟨tree, heightBound⟩ := nonincrease input before result after facts prepared bounded.1 bounded.2.1 done
      exact ⟨extension, available, tree, Nat.le_trans heightBound bounded.2.2⟩)
    inputs before facts prepared bounded outputs after done
  exact ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ related⟩

/-- Retained ordinary column branches preserve the input height bound through actual construction. -/
theorem retained_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (nonincrease : HeightCall call) (limit : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ input ∈ inputs, Bounded limit before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) :
    Extension before after ∧ Bounded limit after result := by
  have branches (values : List (Value Symbol Guard)) (bounded : ∀ input ∈ values, Bounded limit before input)
      (done : (if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) call) before = .done result after) :
      Extension before after ∧ Bounded limit after result := by
    have boundary : values.any recursiveBoundary = false := List.any_eq_false.mpr
      (fun value member => by simp only [tree_boundary value (bounded value member).2.1, Bool.false_eq_true, not_false_eq_true])
    have available : Values before values := fun value member => (bounded value member).1
    have resident : Edges before (values.flatMap nodeEdges) := by
      intro edge member
      obtain ⟨value, included, inner⟩ := List.mem_flatMap.mp member
      exact resident_edges before facts.linked value (available value included).resident edge inner
    have verified := node_verified (values.flatMap nodeEdges) before facts resident
    have extension : Extension before (run (ordinaryUnion values) before).2 :=
      ⟨verified.facts, prepared.preserve (makeNode_noNewMu _ before), verified.growth, verified.history⟩
    have unionAvailable : Available (run (ordinaryUnion values) before).2 (run (ordinaryUnion values) before).1 :=
      verified.result _ _ rfl
    have unionTree := ordinaryUnion_tree values before facts available (fun value member => (bounded value member).2.1)
    have unionBound := ordinaryUnion_bound values before facts.coherent facts.linked
      (fun value member => (available value member).resident) limit (fun value member => (bounded value member).2.2)
    have recursive : call (run (ordinaryUnion values) before).1 (run (ordinaryUnion values) before).2 = .done result after := by
      simpa only [boundary, Bool.false_eq_true, ↓reduceIte, MergedColdMerge.bind, MergedColdMerge.work, Result.bind] using done
    obtain ⟨later, resultAvailable⟩ := checked _ _ result after extension.facts extension.prepared unionAvailable recursive
    obtain ⟨resultTree, resultHeight⟩ := nonincrease _ _ result after extension.facts extension.prepared unionAvailable unionTree recursive
    exact ⟨extension.trans later, resultAvailable, resultTree, Nat.le_trans resultHeight unionBound⟩
  cases inputs with
  | nil => exact branches [] bounded done
  | cons first rest =>
      cases rest with
      | nil =>
          have equal : first = result ∧ before = after := by simpa [retainedColumn, MergedColdMerge.pure] using done
          rcases equal with ⟨rfl, rfl⟩
          exact ⟨.refl before facts prepared, bounded first List.mem_cons_self⟩
      | cons second tail => exact branches (first :: second :: tail) bounded done

/-- Actual ordered filtering only removes original bounded ordinary column operands. -/
theorem column_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (nonincrease : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ input ∈ inputs, Bounded limit before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : column call clear comparison inputs before = .done result after) :
    Extension before after ∧ Bounded limit after result := by
  cases selected : MergedSourceSelection.select clear comparison inputs before with
  | failed => simp only [column, MergedColdMerge.bind, selected, Result.bind, reduceCtorEq] at done
  | done retained middle =>
      have verified := MergedSourceSelection.select_verified clear comparison inputs before facts prepared
        (fun value member => (bounded value member).1)
      rw [selected] at verified
      have extension : Extension before middle :=
        ⟨verified.facts, prepared.preserve verified.unchanged, verified.growth, verified.history⟩
      have subset := MergedSourceSelection.select_subset clear comparison inputs before retained middle selected
      have recursive : retainedColumn call retained middle = .done result after := by
        simpa only [column, MergedColdMerge.bind, selected, Result.bind] using done
      obtain ⟨later, resultBounded⟩ := retained_bounded call checked nonincrease limit retained middle extension.facts extension.prepared
        (fun value member => bounded_grows limit before middle extension value (bounded value (subset value member))) result after recursive
      exact ⟨extension.trans later, resultBounded⟩

/-- Every child of an edge satisfies one ordinary height bound. -/
def EdgeBounded (limit : Nat) (state : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  EdgeResident state edge ∧ ∀ child ∈ edge.children, Tree child ∧ height child ≤ limit

/-- Canonical edge construction keeps the requested complete child list and its height bounds. -/
theorem edge_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (limit : Nat)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (bounded : ∀ value ∈ values, Bounded limit state value) :
    Extension state (run (makeEdge symbol guard values) state).2 ∧
      EdgeBounded limit (run (makeEdge symbol guard values) state).2 (run (makeEdge symbol guard values) state).1 := by
  have available : Values state values := fun value member => (bounded value member).1
  have verified := edge_verified symbol guard values state facts available
  refine ⟨⟨verified.facts, prepared.preserve (by intro key entry body depth ordinary stored; exact stored),
    verified.growth, verified.history⟩, verified.result _ _ rfl, ?_⟩
  rw [InternedShallowValues.makeEdge_children symbol guard values state facts.coherent facts.cached available]
  exact fun value member => (bounded value member).2

/-- Small groups recursively process each child without increasing its ordinary height. -/
theorem small_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (nonincrease : HeightCall call) (limit : Nat)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : EdgeBounded limit before edge) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) :
    Extension before after ∧ EdgeBounded limit after result := by
  cases mapped : MergedColdMerge.map call edge.children before with
  | failed => simp only [small, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done values middle =>
      obtain ⟨extension, valuesBounded⟩ := map_bounded call checked nonincrease limit edge.children before facts prepared
        (fun value member => ⟨facts.cached.edges edge.entry.key edge bounded.1 value member, bounded.2 value member⟩) values middle mapped
      have equal : (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).1 = result ∧
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 = after := by
        simpa only [small, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨later, bounded⟩ := edge_bounded edge.entry.key.symbol edge.entry.key.constraint values limit middle extension.facts extension.prepared valuesBounded
      exact ⟨extension.trans later, bounded⟩

/-- Large groups retain the original maximum child height through their actual source columns. -/
theorem large_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (nonincrease : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ edge ∈ first :: rest, EdgeBounded limit before edge)
    (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : large call clear comparison top first rest before = .done result after) :
    Extension before after ∧ EdgeBounded limit after result := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have inputs : ∀ values ∈ columns, ∀ value ∈ values, Bounded limit before value := by
    intro values member value included
    obtain ⟨row, rowMember, valueMember⟩ := MergedPhysicalGroupEdges.columns_member _ _ values member value included
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp rowMember
    exact ⟨facts.cached.edges edge.entry.key edge (bounded edge edgeMember).1 value valueMember,
      (bounded edge edgeMember).2 value valueMember⟩
  cases mapped : MergedColdMerge.map (column call clear comparison) columns before with
  | failed => simp only [large, columns, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done values middle =>
      obtain ⟨extension, related⟩ := map_valid (column call clear comparison)
        (fun state inputs => ∀ input ∈ inputs, Bounded limit state input) (fun state _ result => Bounded limit state result)
        (fun before after extension inputs bounded input member => bounded_grows limit before after extension input (bounded input member))
        (fun before after extension _ result bounded => bounded_grows limit before after extension result bounded)
        (fun inputs before result after facts prepared bounded done =>
          column_bounded call checked nonincrease limit clear comparison inputs before facts prepared bounded result after done)
        columns before facts prepared inputs values middle mapped
      have equal : (run (makeEdge first.entry.key.symbol top values) middle).1 = result ∧
          (run (makeEdge first.entry.key.symbol top values) middle).2 = after := by
        simpa only [large, columns, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨later, bounded⟩ := edge_bounded first.entry.key.symbol top values limit middle extension.facts extension.prepared
        (EnumerationSoundness.all₂_outputs _ _ _ related)
      exact ⟨extension.trans later, bounded⟩

/-- Cache extension preserves each complete edge's ordinary shape and height. -/
theorem edgeBounded_grows (limit : Nat) (before after : State Symbol Guard) (extension : Extension before after)
    (edge : EdgeValue Symbol Guard) (bounded : EdgeBounded limit before edge) : EdgeBounded limit after edge :=
  ⟨edge_grows before after extension.growth edge bounded.1, bounded.2⟩

/-- Both actual threshold branches retain the original maximum child height. -/
theorem group_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (nonincrease : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ edge ∈ edges, EdgeBounded limit before edge)
    (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : group call clear comparison top edges before = .done results after) :
    Extension before after ∧ ∀ edge ∈ results, EdgeBounded limit after edge := by
  by_cases smallGroup : edges.length ≤ 4
  · obtain ⟨extension, related⟩ := map_valid (small call) (EdgeBounded limit) (fun state _ result => EdgeBounded limit state result)
      (edgeBounded_grows limit) (fun before after extension _ result bounded => edgeBounded_grows limit before after extension result bounded)
      (fun edge before result after facts prepared bounded done => small_bounded call checked nonincrease limit edge before facts prepared bounded result after done)
      edges before facts prepared bounded results after (by simpa only [group, ite_eq_left smallGroup] using done)
    exact ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ related⟩
  · cases edges with
    | nil => simp at smallGroup
    | cons first rest =>
        cases built : large call clear comparison top first rest before with
        | failed => simp only [group, ite_eq_right smallGroup, MergedColdMerge.bind, built, Result.bind, reduceCtorEq] at done
        | done result final =>
            have equal : [result] = results ∧ final = after := by
              simpa only [group, ite_eq_right smallGroup, MergedColdMerge.bind, built, Result.bind, MergedColdMerge.pure, Result.done.injEq] using done
            rcases equal with ⟨rfl, rfl⟩
            obtain ⟨extension, valid⟩ := large_bounded call checked nonincrease limit clear comparison top first rest before facts prepared bounded result final built
            exact ⟨extension, fun edge member => (List.mem_singleton.mp member).symm ▸ valid⟩

/-- Final ordinary construction adds at most one layer above the original child height bound. -/
theorem root_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (nonincrease : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (groups : List (List (EdgeValue Symbol Guard)))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ group ∈ groups, ∀ edge ∈ group, EdgeBounded limit before edge)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root call clear comparison top groups before = .done result after) : Tree result ∧ height result ≤ limit + 1 := by
  cases mapped : MergedColdMerge.map (group call clear comparison top) groups before with
  | failed => simp only [root, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done rows middle =>
      obtain ⟨extension, related⟩ := map_valid (group call clear comparison top)
        (fun state edges => ∀ edge ∈ edges, EdgeBounded limit state edge)
        (fun state _ results => ∀ edge ∈ results, EdgeBounded limit state edge)
        (fun before after extension edges valid edge member => edgeBounded_grows limit before after extension edge (valid edge member))
        (fun before after extension _ edges valid edge member => edgeBounded_grows limit before after extension edge (valid edge member))
        (fun edges before results after facts prepared bounded done =>
          group_bounded call checked nonincrease limit clear comparison top edges before facts prepared bounded results after done)
        groups before facts prepared bounded rows middle mapped
      have rowBounded := EnumerationSoundness.all₂_outputs _ _ _ related
      have allBounded : ∀ edge ∈ rows.flatten, EdgeBounded limit middle edge := by
        intro edge member
        obtain ⟨row, present, included⟩ := List.mem_flatten.mp member
        exact rowBounded row present edge included
      have equal : (run (makeNode rows.flatten) middle).1 = result ∧ (run (makeNode rows.flatten) middle).2 = after := by
        simpa only [root, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      constructor
      · exact makeNode_tree _ middle extension.facts (fun edge member => (allBounded edge member).1)
          (fun edge member child included => ((allBounded edge member).2 child included).1)
      · apply makeNode_bound _ middle extension.facts.coherent extension.facts.linked
          (fun edge member => (allBounded edge member).1) (limit + 1)
        intro edge member
        have bounded : edgeHeight edge ≤ limit := by
          cases edge with
          | mk entry children =>
              exact (childrenHeight_le children limit).mpr
                (fun child included => ((allBounded _ member).2 child included).2)
        omega

/-- Actual successful cold calls preserve finite ordinary trees and cannot increase their height. -/
theorem worker_height [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat) :
    HeightCall (worker grouping clear top ordinary comparison) := by
  induction ordinary with
  | zero =>
      intro input before result after facts prepared available tree done
      cases tree with
      | empty => cases done; exact ⟨.empty, Nat.le_refl _⟩
      | node entry edges depth free children =>
          by_cases closed : free = []
          · simp [worker, closed] at done
          · simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done
            rcases done with ⟨rfl, rfl⟩
            exact ⟨.node entry edges depth free children, Nat.le_refl _⟩
  | succ ordinary ih =>
      intro input before result after facts prepared available tree done
      cases tree with
      | empty => cases done; exact ⟨.empty, Nat.le_refl _⟩
      | node entry edges depth free children =>
          by_cases closed : free = []
          · subst free
            apply root_bounded (worker grouping clear top ordinary comparison)
              (worker_valid grouping correct clear top ordinary comparison) ih (edgesHeight edges)
              clear comparison top (grouping edges) before facts prepared _ result after
              (by simpa only [worker, ↓reduceIte] using done)
            intro group groupMember edge edgeMember
            have member := (correct edges).partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, groupMember, edgeMember⟩)
            refine ⟨resident_edges before facts.linked _ available.resident edge member, ?_⟩
            intro child included
            refine ⟨children edge member child included, ?_⟩
            have below := child_lt entry edges depth [] edge member child included
            simp only [height] at below
            omega
          · simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done
            rcases done with ⟨rfl, rfl⟩
            exact ⟨.node entry edges depth free children, Nat.le_refl _⟩

/-- The source successful-call relation inherits the fully derived ordinary height theorem. -/
theorem merge_height [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (input result : Value Symbol Guard)
    (tree : Tree input) (done : EqualityMergedTargetShape.Merge grouping clear top input result) :
    Tree result ∧ height result ≤ height input := by
  obtain ⟨ordinary, comparison, before, after, facts, prepared, available, done⟩ := done
  exact worker_height grouping correct clear top ordinary comparison input before result after facts prepared available tree done

end MicroCFTA.EqualityMergedTargetHeight
