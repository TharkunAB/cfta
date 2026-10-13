import MicroCFTA.MergedColdMergeMapFacts
import MicroCFTA.EqualityMergedTargetLayers
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Actual recursive child images below small merge roots

When every source group has at most four rows, the worker calls itself
on each original child. Canonical edge and node readback can remove rows,
but each returned child still comes from one of these actual calls.
-/
namespace MicroCFTA.EqualityMergedTargetShape
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedColdMergeMapFacts Language

/-- Record a completed actual callback and its available input in a prepared source cache. -/
def Called (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (input result : Value Symbol Guard) : Prop :=
  ∃ before after, Facts before ∧ Prepared before ∧ Available before input ∧ call input before = .done result after

/-- Each output position of related lists has an original input position. -/
theorem related_member {Input Output : Type} (relation : Input → Output → Prop)
    (inputs : List Input) (outputs : List Output) (related : All₂ relation inputs outputs)
    (output : Output) (member : output ∈ outputs) : ∃ input ∈ inputs, relation input output := by
  induction related with
  | nil => contradiction
  | @cons first value rest remaining head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨first, List.mem_cons_self, head⟩
      · obtain ⟨input, included, property⟩ := ih member
        exact ⟨input, List.mem_cons_of_mem _ included, property⟩

/-- Ordered child traversal records each exact completed callback as well as later availability. -/
theorem map_called (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (available : Values before inputs)
    (outputs : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : MergedColdMerge.map call inputs before = .done outputs after) :
    Extension before after ∧ All₂ (fun input result => Available after result ∧ Called call input result) inputs outputs := by
  apply map_valid call Available (fun state input result => Available state result ∧ Called call input result)
    (fun _ _ extension value available => extension.available value available)
    (fun _ _ extension _ result post => ⟨extension.available result post.1, post.2⟩)
    _ inputs before facts prepared available outputs after done
  intro input initial result final initialFacts initialPrepared inputAvailable completed
  obtain ⟨extension, resultAvailable⟩ := checked input initial result final initialFacts initialPrepared inputAvailable completed
  exact ⟨extension, resultAvailable, initial, final, initialFacts, initialPrepared, inputAvailable, completed⟩

/-- A completed small-edge result contains only outputs of actual original-child calls. -/
theorem small_image [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid call)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : EdgeResident before edge) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) :
    Extension before after ∧ EdgeResident after result ∧
      ∀ child ∈ result.children, ∃ input ∈ edge.children, Called call input child := by
  cases mapped : MergedColdMerge.map call edge.children before with
  | failed => simp only [small, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done values middle =>
      obtain ⟨extension, related⟩ := map_called call checked edge.children before facts prepared
        (facts.cached.edges edge.entry.key edge resident) values middle mapped
      have inputs : Values middle values := EnumerationSoundness.all₂_outputs _ _ _
        (related.imp (fun _ _ post => post.1))
      have verified := edge_verified edge.entry.key.symbol edge.entry.key.constraint values middle extension.facts inputs
      have constructed : Extension middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 :=
        ⟨verified.facts, extension.prepared.preserve (by intro key entry body depth ordinary stored; exact stored),
          verified.growth, verified.history⟩
      have equal : (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).1 = result ∧
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 = after := by
        simpa only [small, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      refine ⟨extension.trans constructed, verified.result _ _ rfl, ?_⟩
      intro child member
      rw [InternedShallowValues.makeEdge_children _ _ values middle extension.facts.coherent extension.facts.cached inputs] at member
      obtain ⟨input, included, post⟩ := related_member _ _ _ related child member
      exact ⟨input, included, post.2⟩

/-- A small group retains the original edge for every output-child call witness. -/
theorem group_small_image [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid call)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (smallGroup : edges.length ≤ 4) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : Edges before edges) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : group call clear comparison top edges before = .done results after) :
    Extension before after ∧ Edges after results ∧
      ∀ result ∈ results, ∀ child ∈ result.children,
        ∃ edge ∈ edges, ∃ input ∈ edge.children, Called call input child := by
  have mapped : MergedColdMerge.map (small call) edges before = .done results after := by
    simpa only [group, ite_eq_left smallGroup] using done
  obtain ⟨extension, related⟩ := map_valid (small call) EdgeResident
    (fun state edge result => EdgeResident state result ∧
      ∀ child ∈ result.children, ∃ input ∈ edge.children, Called call input child)
    (fun before after extension edge resident => edge_grows before after extension.growth edge resident)
    (fun before after extension _ result post => ⟨edge_grows before after extension.growth result post.1, post.2⟩)
    (fun edge before result after facts prepared resident done => small_image call checked edge before facts prepared resident result after done)
    edges before facts prepared resident results after mapped
  refine ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ (related.imp (fun _ _ post => post.1)), ?_⟩
  intro result member child included
  obtain ⟨edge, present, post⟩ := related_member _ _ _ related result member
  obtain ⟨input, inputMember, called⟩ := post.2 child included
  exact ⟨edge, present, input, inputMember, called⟩

/-- Final node normalization retains the actual original-child call behind each surviving child. -/
theorem root_small_image [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid call)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (groups : List (List (EdgeValue Symbol Guard)))
    (smallGroups : ∀ group ∈ groups, group.length ≤ 4)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : ∀ group ∈ groups, Edges before group) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root call clear comparison top groups before = .done result after) :
    ∀ child ∈ (nodeEdges result).flatMap EdgeValue.children,
      ∃ group ∈ groups, ∃ edge ∈ group, ∃ input ∈ edge.children, Called call input child := by
  cases mapped : MergedColdMerge.map (group call clear comparison top) groups before with
  | failed => simp only [root, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done rows middle =>
      let pre := fun (state : State Symbol Guard) (edges : List (EdgeValue Symbol Guard)) =>
        Edges state edges ∧ edges.length ≤ 4
      let post := fun (state : State Symbol Guard) (edges results : List (EdgeValue Symbol Guard)) =>
        Edges state results ∧ ∀ result ∈ results, ∀ child ∈ result.children,
          ∃ edge ∈ edges, ∃ input ∈ edge.children, Called call input child
      obtain ⟨extension, related⟩ := map_valid (group call clear comparison top) pre post
        (fun before after extension edges valid =>
          ⟨fun edge member => edge_grows before after extension.growth edge (valid.1 edge member), valid.2⟩)
        (fun before after extension _ results valid =>
          ⟨fun edge member => edge_grows before after extension.growth edge (valid.1 edge member), valid.2⟩)
        (fun edges before results after facts prepared valid done =>
          group_small_image call checked clear comparison top edges valid.2 before facts prepared valid.1 results after done)
        groups before facts prepared (fun group member => ⟨resident group member, smallGroups group member⟩) rows middle mapped
      have rowInputs : ∀ row ∈ rows, Edges middle row :=
        EnumerationSoundness.all₂_outputs _ _ _ (related.imp (fun _ _ valid => valid.1))
      have allInputs : Edges middle rows.flatten := by
        intro edge member
        obtain ⟨row, included, inner⟩ := List.mem_flatten.mp member
        exact rowInputs row included edge inner
      have equal : (run (makeNode rows.flatten) middle).1 = result ∧ (run (makeNode rows.flatten) middle).2 = after := by
        simpa only [root, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      intro child member
      obtain ⟨edge, present, included⟩ := List.mem_flatMap.mp member
      rw [EqualityLeafProjectionPhysical.makeNode_edges _ middle extension.facts.coherent extension.facts.linked allInputs] at present
      have original := (List.mem_filter.mp (canonicalEdges_member _ edge present)).1
      obtain ⟨row, rowMember, edgeMember⟩ := List.mem_flatten.mp original
      obtain ⟨group, groupMember, post⟩ := related_member _ _ _ related row rowMember
      obtain ⟨source, sourceMember, input, inputMember, called⟩ := post.2 edge edgeMember child included
      exact ⟨group, groupMember, source, sourceMember, input, inputMember, called⟩

/-- The merge relation includes only actual successful calls on available prepared source inputs. -/
def Merge [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (clear : Guard → Bool) (top : Guard) (input result : Value Symbol Guard) : Prop :=
  ∃ ordinary comparison, Called (worker grouping clear top ordinary comparison) input result

/-- Actual cold merging satisfies the small-root child-image obligation without recursive premises. -/
theorem worker_small_children [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (input result : Value Symbol Guard)
    (done : Merge grouping clear top input result)
    (smallGroups : ∀ entry edges depth, input = .node entry edges depth [] → ∀ group ∈ grouping edges, group.length ≤ 4) :
    ∀ child ∈ EqualityMergedTargetLayers.children result,
      ∃ original ∈ EqualityMergedTargetLayers.children input, Merge grouping clear top original child := by
  obtain ⟨ordinary, comparison, before, after, facts, prepared, available, done⟩ := done
  cases input with
  | empty | reference | union | mu =>
      simp only [worker, MergedColdMerge.pure, Result.done.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      simp [EqualityMergedTargetLayers.children]
  | node entry edges depth free =>
      by_cases closed : free = []
      · subst free
        cases ordinary with
        | zero => simp [worker] at done
        | succ remaining =>
            have source := root_small_image (worker grouping clear top remaining comparison)
              (worker_valid grouping correct clear top remaining comparison) clear comparison top (grouping edges)
              (smallGroups entry edges depth rfl) before facts prepared
              (fun group included edge member => resident_edges before facts.linked _ available.resident edge
                ((correct edges).partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, included, member⟩)))
              result after (by simpa only [worker, ↓reduceIte] using done)
            intro child member
            have outputChild : child ∈ (nodeEdges result).flatMap EdgeValue.children := by
              cases result <;> simp_all [EqualityMergedTargetLayers.children, nodeEdges]
            obtain ⟨group, groupMember, edge, edgeMember, original, originalMember, called⟩ := source child outputChild
            refine ⟨original, ?_, remaining, comparison, called⟩
            simp only [EqualityMergedTargetLayers.children, ↓reduceIte]
            exact List.mem_flatMap.mpr ⟨edge,
              (correct edges).partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, groupMember, edgeMember⟩), originalMember⟩
      · cases ordinary <;>
          simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done <;>
          rcases done with ⟨rfl, rfl⟩ <;>
          simp [EqualityMergedTargetLayers.children, closed]

end MicroCFTA.EqualityMergedTargetShape
