import MicroCFTA.MergedColdMergeMapFacts
import MicroCFTA.SourceSynthesisUniversePrefixHeight

/-!
# Ordinary and union height after actual cold merging

The actual worker stops at Mu, reference, and explicit union roots.
A recursive-boundary column can add one union layer and stops recursion.
Other columns recurse after ordinary-row concatenation. The complete
successful worker adds at most one layer above its input height.
-/
namespace MicroCFTA.MergedPrefixHeight
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedColdMergeMapFacts
open MergedOrdinaryHeight (recursiveBoundary ordinaryUnion)
open SourceSynthesisUniversePrefixHeight
open Language

variable {Symbol Guard : Type}

/-- A completed recursive call adds at most one ordinary or union layer. -/
def HeightCall (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ input before result after, Facts before → Prepared before → Available before input →
    call input before = .done result after → height result ≤ height input + 1

/-- A returned height bound retains the actual record availability. -/
def Bounded (limit : Nat) (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  Available state value ∧ height value ≤ limit

/-- Complete values retain their height through actual cache extension. -/
theorem bounded_grows (limit : Nat) (before after : State Symbol Guard) (extension : Extension before after)
    (value : Value Symbol Guard) (bounded : Bounded limit before value) : Bounded limit after value :=
  ⟨extension.available value bounded.1, bounded.2⟩

/-- Existing ordered map facts transport a common input bound with one output layer. -/
theorem map_bounded (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (oneLayer : HeightCall call) (limit : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ input ∈ inputs, Bounded limit before input)
    (outputs : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : MergedColdMerge.map call inputs before = .done outputs after) :
    Extension before after ∧ ∀ output ∈ outputs, Bounded (limit + 1) after output := by
  obtain ⟨extension, related⟩ := map_valid call (Bounded limit) (fun state _ result => Bounded (limit + 1) state result)
    (bounded_grows limit)
    (fun before after extension _ result bounded => bounded_grows (limit + 1) before after extension result bounded)
    (fun input before result after facts prepared bounded done => by
      obtain ⟨extension, available⟩ := checked input before result after facts prepared bounded.1 done
      have below := oneLayer input before result after facts prepared bounded.1 done
      exact ⟨extension, available, Nat.le_trans below (Nat.add_le_add_right bounded.2 1)⟩)
    inputs before facts prepared bounded outputs after done
  exact ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ related⟩

/-- Both literal column branches add at most one layer above the retained inputs. -/
theorem retained_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (oneLayer : HeightCall call) (limit : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ input ∈ inputs, Bounded limit before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) :
    Extension before after ∧ Bounded (limit + 1) after result := by
  have branches (values : List (Value Symbol Guard)) (bounded : ∀ input ∈ values, Bounded limit before input)
      (done : (if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) call) before = .done result after) :
      Extension before after ∧ Bounded (limit + 1) after result := by
    have available : Values before values := fun value member => (bounded value member).1
    have maximum : childrenHeight values ≤ limit :=
      (childrenHeight_le values limit).mpr (fun value member => (bounded value member).2)
    by_cases boundary : values.any recursiveBoundary = true
    · have equal : (run (makeUnion values) before).1 = result ∧
          (run (makeUnion values) before).2 = after := by
        simpa only [ite_eq_left boundary, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      have verified := union_verified values before facts available
      have extension : Extension before (run (makeUnion values) before).2 :=
        ⟨verified.facts, prepared.preserve (makeUnion_noNewMu values before), verified.growth, verified.history⟩
      refine ⟨extension, verified.result _ _ rfl, ?_⟩
      exact Nat.le_trans (makeUnion_bound values before facts available) (Nat.add_le_add_right maximum 1)
    · have resident : ∀ edge ∈ values.flatMap nodeEdges, EdgeResident before edge := by
        intro edge member
        obtain ⟨value, included, inner⟩ := List.mem_flatMap.mp member
        exact resident_edges before facts.linked value (available value included).resident edge inner
      have verified := node_verified (values.flatMap nodeEdges) before facts resident
      have extension : Extension before (run (ordinaryUnion values) before).2 :=
        ⟨verified.facts, prepared.preserve (makeNode_noNewMu _ before), verified.growth, verified.history⟩
      have unionAvailable : Available (run (ordinaryUnion values) before).2 (run (ordinaryUnion values) before).1 :=
        verified.result _ _ rfl
      have unionBound : height (run (ordinaryUnion values) before).1 ≤ limit :=
        Nat.le_trans (ordinaryUnion_bound values before facts (fun value member => (available value member).resident)) maximum
      have recursive : call (run (ordinaryUnion values) before).1 (run (ordinaryUnion values) before).2 =
          .done result after := by
        simpa only [ite_eq_right boundary, MergedColdMerge.bind, MergedColdMerge.work, Result.bind] using done
      obtain ⟨later, resultAvailable⟩ := checked _ _ result after extension.facts extension.prepared unionAvailable recursive
      have resultHeight := oneLayer _ _ result after extension.facts extension.prepared unionAvailable recursive
      exact ⟨extension.trans later, resultAvailable, Nat.le_trans resultHeight (Nat.add_le_add_right unionBound 1)⟩
  cases inputs with
  | nil => exact branches [] bounded done
  | cons first rest =>
      cases rest with
      | nil =>
          have equal : first = result ∧ before = after := by
            simpa only [retainedColumn, MergedColdMerge.pure, Result.done.injEq] using done
          rcases equal with ⟨rfl, rfl⟩
          exact ⟨.refl before facts prepared, (bounded first List.mem_cons_self).1,
            Nat.le_trans (bounded first List.mem_cons_self).2 (Nat.le_succ limit)⟩
      | cons second tail => exact branches (first :: second :: tail) bounded done

/-- Actual ordered filtering only removes operands before column reconstruction. -/
theorem column_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (oneLayer : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ input ∈ inputs, Bounded limit before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : column call clear comparison inputs before = .done result after) :
    Extension before after ∧ Bounded (limit + 1) after result := by
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
      obtain ⟨later, resultBounded⟩ := retained_bounded call checked oneLayer limit retained middle extension.facts extension.prepared
        (fun value member => bounded_grows limit before middle extension value (bounded value (subset value member))) result after recursive
      exact ⟨extension.trans later, resultBounded⟩

/-- Every actual child of an edge satisfies the stated prefix-height bound. -/
def EdgeBounded (limit : Nat) (state : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  EdgeResident state edge ∧ ∀ child ∈ edge.children, height child ≤ limit

/-- Actual edge construction retains the requested complete child list and bound. -/
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

/-- Small groups add at most one layer below each retained original edge. -/
theorem small_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (oneLayer : HeightCall call) (limit : Nat)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : EdgeBounded limit before edge) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) :
    Extension before after ∧ EdgeBounded (limit + 1) after result := by
  cases mapped : MergedColdMerge.map call edge.children before with
  | failed => simp only [small, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done values middle =>
      obtain ⟨extension, valuesBounded⟩ := map_bounded call checked oneLayer limit edge.children before facts prepared
        (fun value member => ⟨facts.cached.edges edge.entry.key edge bounded.1 value member, bounded.2 value member⟩)
        values middle mapped
      have equal : (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).1 = result ∧
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 = after := by
        simpa only [small, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨later, resultBounded⟩ := edge_bounded edge.entry.key.symbol edge.entry.key.constraint values
        (limit + 1) middle extension.facts extension.prepared valuesBounded
      exact ⟨extension.trans later, resultBounded⟩

/-- Large groups add at most one layer in each actual source column. -/
theorem large_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (oneLayer : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ edge ∈ first :: rest, EdgeBounded limit before edge)
    (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : large call clear comparison top first rest before = .done result after) :
    Extension before after ∧ EdgeBounded (limit + 1) after result := by
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
        (fun state inputs => ∀ input ∈ inputs, Bounded limit state input)
        (fun state _ result => Bounded (limit + 1) state result)
        (fun before after extension inputs bounded input member => bounded_grows limit before after extension input (bounded input member))
        (fun before after extension _ result bounded => bounded_grows (limit + 1) before after extension result bounded)
        (fun inputs before result after facts prepared bounded done =>
          column_bounded call checked oneLayer limit clear comparison inputs before facts prepared bounded result after done)
        columns before facts prepared inputs values middle mapped
      have equal : (run (makeEdge first.entry.key.symbol top values) middle).1 = result ∧
          (run (makeEdge first.entry.key.symbol top values) middle).2 = after := by
        simpa only [large, columns, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨later, resultBounded⟩ := edge_bounded first.entry.key.symbol top values (limit + 1)
        middle extension.facts extension.prepared (EnumerationSoundness.all₂_outputs _ _ _ related)
      exact ⟨extension.trans later, resultBounded⟩

/-- Actual cache extension preserves every complete edge and its height bound. -/
theorem edgeBounded_grows (limit : Nat) (before after : State Symbol Guard) (extension : Extension before after)
    (edge : EdgeValue Symbol Guard) (bounded : EdgeBounded limit before edge) : EdgeBounded limit after edge :=
  ⟨edge_grows before after extension.growth edge bounded.1, bounded.2⟩

/-- Both actual threshold branches retain the same one-layer bound. -/
theorem group_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (oneLayer : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ edge ∈ edges, EdgeBounded limit before edge)
    (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : group call clear comparison top edges before = .done results after) :
    Extension before after ∧ ∀ edge ∈ results, EdgeBounded (limit + 1) after edge := by
  by_cases smallGroup : edges.length ≤ 4
  · obtain ⟨extension, related⟩ := map_valid (small call) (EdgeBounded limit)
      (fun state _ result => EdgeBounded (limit + 1) state result)
      (edgeBounded_grows limit)
      (fun before after extension _ result bounded => edgeBounded_grows (limit + 1) before after extension result bounded)
      (fun edge before result after facts prepared bounded done => small_bounded call checked oneLayer limit edge before facts prepared bounded result after done)
      edges before facts prepared bounded results after (by simpa only [group, ite_eq_left smallGroup] using done)
    exact ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ related⟩
  · cases edges with
    | nil => simp at smallGroup
    | cons first rest =>
        cases built : large call clear comparison top first rest before with
        | failed => simp only [group, ite_eq_right smallGroup, MergedColdMerge.bind, built, Result.bind, reduceCtorEq] at done
        | done result final =>
            have equal : [result] = results ∧ final = after := by
              simpa only [group, ite_eq_right smallGroup, MergedColdMerge.bind, built, Result.bind,
                MergedColdMerge.pure, Result.done.injEq] using done
            rcases equal with ⟨rfl, rfl⟩
            obtain ⟨extension, valid⟩ := large_bounded call checked oneLayer limit clear comparison top
              first rest before facts prepared bounded result final built
            exact ⟨extension, fun edge member => (List.mem_singleton.mp member).symm ▸ valid⟩

/-- Final node construction adds its ordinary layer above the returned child bound. -/
theorem root_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (oneLayer : HeightCall call) (limit : Nat)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (groups : List (List (EdgeValue Symbol Guard)))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ group ∈ groups, ∀ edge ∈ group, EdgeBounded limit before edge)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root call clear comparison top groups before = .done result after) : height result ≤ limit + 2 := by
  cases mapped : MergedColdMerge.map (group call clear comparison top) groups before with
  | failed => simp only [root, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done rows middle =>
      obtain ⟨extension, related⟩ := map_valid (group call clear comparison top)
        (fun state edges => ∀ edge ∈ edges, EdgeBounded limit state edge)
        (fun state _ results => ∀ edge ∈ results, EdgeBounded (limit + 1) state edge)
        (fun before after extension edges valid edge member => edgeBounded_grows limit before after extension edge (valid edge member))
        (fun before after extension _ edges valid edge member => edgeBounded_grows (limit + 1) before after extension edge (valid edge member))
        (fun edges before results after facts prepared bounded done =>
          group_bounded call checked oneLayer limit clear comparison top edges before facts prepared bounded results after done)
        groups before facts prepared bounded rows middle mapped
      have rowBounded := EnumerationSoundness.all₂_outputs _ _ _ related
      have allBounded : ∀ edge ∈ rows.flatten, EdgeBounded (limit + 1) middle edge := by
        intro edge member
        obtain ⟨row, present, included⟩ := List.mem_flatten.mp member
        exact rowBounded row present edge included
      have equal : (run (makeNode rows.flatten) middle).1 = result ∧ (run (makeNode rows.flatten) middle).2 = after := by
        simpa only [root, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      apply makeNode_bound _ middle extension.facts (fun edge member => (allBounded edge member).1) (limit + 2)
      intro edge member
      have below : edgeHeight edge ≤ limit + 1 := by
        cases edge with
        | mk entry children => exact (childrenHeight_le children (limit + 1)).mpr (allBounded _ member).2
      omega

/-- Every actual successful worker call adds at most one ordinary or union layer. -/
theorem worker_height [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat) :
    HeightCall (worker grouping clear top ordinary comparison) := by
  induction ordinary with
  | zero =>
      intro input before result after facts prepared available done
      cases input with
      | empty | reference | union | mu => cases done; exact Nat.le_succ _
      | node entry edges depth free =>
          by_cases closed : free = []
          · simp only [worker, closed, ↓reduceIte, reduceCtorEq] at done
          · simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done
            rcases done with ⟨rfl, rfl⟩
            exact Nat.le_succ _
  | succ ordinary ih =>
      intro input before result after facts prepared available done
      cases input with
      | empty | reference | union | mu => cases done; exact Nat.le_succ _
      | node entry edges depth free =>
          by_cases closed : free = []
          · subst free
            have bounded : ∀ group ∈ grouping edges, ∀ edge ∈ group, EdgeBounded (edgesHeight edges) before edge := by
              intro group groupMember edge edgeMember
              have member := (correct edges).partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, groupMember, edgeMember⟩)
              refine ⟨resident_edges before facts.linked _ available.resident edge member, ?_⟩
              intro child included
              have less := child_lt entry edges depth [] edge member child included
              simp only [height] at less
              omega
            have below := root_bounded (worker grouping clear top ordinary comparison)
              (worker_valid grouping correct clear top ordinary comparison) ih (edgesHeight edges)
              clear comparison top (grouping edges) before facts prepared bounded result after
              (by simpa only [worker, ↓reduceIte] using done)
            simpa only [height, Nat.add_assoc] using below
          · simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done
            rcases done with ⟨rfl, rfl⟩
            exact Nat.le_succ _

end MicroCFTA.MergedPrefixHeight
