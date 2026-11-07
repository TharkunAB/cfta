import MicroCFTA.EqualityMergedTargetShape
import MicroCFTA.InternedBoundaryAtoms

/-!
# Boundary atoms after the actual cold merge

Every successful merge output uses boundary atoms from its input.
The proof includes literal references, Mu records, and explicit unions.
It follows both retained-column branches and every ordered row group.
The successful-call premise is internal to the source merge composition.
-/
namespace MicroCFTA.MergedPrefixAtoms
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedColdMergeMapFacts
open MergedOrdinaryHeight InternedBoundaryAtoms Language
open InternedBinderProtocol (NodeRef)

/-- Every returned boundary atom belongs to the actual recursive input. -/
def AtomCall (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ input before result after, Facts before → Prepared before → Available before input →
    call input before = .done result after → ∀ atom ∈ atoms result, atom ∈ atoms input

/-- A common source list contains every boundary atom of this complete value. -/
def Within (source : List NodeRef) (value : Value Symbol Guard) : Prop :=
  ∀ atom ∈ atoms value, atom ∈ source

/-- A bounded value also retains actual availability in its current heap. -/
def Bounded (source : List NodeRef) (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  Available state value ∧ Within source value

/-- Actual cache extension preserves a complete value and its boundary atoms. -/
theorem bounded_grows (source : List NodeRef) (before after : State Symbol Guard)
    (extension : Extension before after) (value : Value Symbol Guard)
    (bounded : Bounded source before value) : Bounded source after value :=
  ⟨extension.available value bounded.1, bounded.2⟩

/-- An outgoing ordinary child retains its boundary atoms in its original value. -/
theorem child_atom (value : Value Symbol Guard) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ nodeEdges value) (child : Value Symbol Guard) (included : child ∈ edge.children)
    (atom : NodeRef) (present : atom ∈ atoms child) : atom ∈ atoms value := by
  cases value with
  | empty | reference | union | mu => simp only [nodeEdges, List.not_mem_nil] at member
  | node entry edges depth free =>
      simpa only [atoms] using (edge_member edges atom).mpr ⟨edge, member, child, included, present⟩

/-- Ordinary column construction retains atoms from actual original operands. -/
theorem ordinaryUnion_atoms [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : Values state values) (atom : NodeRef)
    (present : atom ∈ atoms (run (ordinaryUnion values) state).1) :
    ∃ value ∈ values, atom ∈ atoms value := by
  have resident : Edges state (values.flatMap nodeEdges) := by
    intro edge member
    obtain ⟨value, included, inner⟩ := List.mem_flatMap.mp member
    exact resident_edges state facts.linked value (available value included).resident edge inner
  have original := makeNode_atom_origin (values.flatMap nodeEdges) state facts.coherent facts.linked
    resident atom present
  obtain ⟨edge, member, child, included, occurrence⟩ := (edge_member _ atom).mp original
  obtain ⟨value, valueMember, edgeMember⟩ := List.mem_flatMap.mp member
  exact ⟨value, valueMember, child_atom value edge edgeMember child included atom occurrence⟩

/-- Ordered recursive calls preserve the common original atom list. -/
theorem map_bounded (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (origin : AtomCall call) (source : List NodeRef)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (bounded : ∀ input ∈ inputs, Bounded source before input)
    (outputs : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : MergedColdMerge.map call inputs before = .done outputs after) :
    Extension before after ∧ ∀ output ∈ outputs, Bounded source after output := by
  obtain ⟨extension, related⟩ := map_valid call (Bounded source)
    (fun state _ result => Bounded source state result) (bounded_grows source)
    (fun before after extension _ result bounded => bounded_grows source before after extension result bounded)
    (fun input before result after facts prepared bounded done => by
      obtain ⟨extension, available⟩ := checked input before result after facts prepared bounded.1 done
      exact ⟨extension, available, fun atom present => bounded.2 atom
        (origin input before result after facts prepared bounded.1 done atom present)⟩)
    inputs before facts prepared bounded outputs after done
  exact ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ related⟩

/-- Singleton, recursive-union, and ordinary-union columns retain original atoms. -/
theorem retained_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (origin : AtomCall call) (source : List NodeRef)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (bounded : ∀ input ∈ inputs, Bounded source before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) :
    Extension before after ∧ Bounded source after result := by
  have branches (values : List (Value Symbol Guard))
      (bounded : ∀ input ∈ values, Bounded source before input)
      (done : (if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) call) before = .done result after) :
      Extension before after ∧ Bounded source after result := by
    have available : Values before values := fun value member => (bounded value member).1
    cases boundary : values.any recursiveBoundary with
    | true =>
        have equal : (run (makeUnion values) before).1 = result ∧
            (run (makeUnion values) before).2 = after := by
          simpa only [boundary, ↓reduceIte, MergedColdMerge.work, Result.done.injEq] using done
        rcases equal with ⟨rfl, rfl⟩
        have verified := union_verified values before facts available
        refine ⟨⟨verified.facts, prepared.preserve (makeUnion_noNewMu values before),
          verified.growth, verified.history⟩, verified.result _ _ rfl, ?_⟩
        intro atom present
        obtain ⟨value, member, occurrence⟩ := makeUnion_atom_origin values before facts.coherent facts.cached
          facts.linked available atom present
        exact (bounded value member).2 atom occurrence
    | false =>
        have resident : Edges before (values.flatMap nodeEdges) := by
          intro edge member
          obtain ⟨value, included, inner⟩ := List.mem_flatMap.mp member
          exact resident_edges before facts.linked value (available value included).resident edge inner
        have verified := node_verified (values.flatMap nodeEdges) before facts resident
        have extension : Extension before (run (ordinaryUnion values) before).2 :=
          ⟨verified.facts, prepared.preserve (makeNode_noNewMu _ before), verified.growth, verified.history⟩
        have unionAvailable : Available (run (ordinaryUnion values) before).2
            (run (ordinaryUnion values) before).1 := verified.result _ _ rfl
        have unionWithin : Within source (run (ordinaryUnion values) before).1 := by
          intro atom present
          obtain ⟨value, member, occurrence⟩ := ordinaryUnion_atoms values before facts available atom present
          exact (bounded value member).2 atom occurrence
        have recursive : call (run (ordinaryUnion values) before).1
            (run (ordinaryUnion values) before).2 = .done result after := by
          simpa only [boundary, Bool.false_eq_true, ↓reduceIte, MergedColdMerge.bind,
            MergedColdMerge.work, Result.bind] using done
        obtain ⟨later, resultAvailable⟩ := checked _ _ result after extension.facts extension.prepared unionAvailable recursive
        refine ⟨extension.trans later, resultAvailable, ?_⟩
        intro atom present
        exact unionWithin atom (origin _ _ result after extension.facts extension.prepared unionAvailable recursive atom present)
  cases inputs with
  | nil => exact branches [] bounded done
  | cons first rest =>
      cases rest with
      | nil =>
          have equal : first = result ∧ before = after := by simpa [retainedColumn, MergedColdMerge.pure] using done
          rcases equal with ⟨rfl, rfl⟩
          exact ⟨.refl before facts prepared, bounded first List.mem_cons_self⟩
      | cons second tail => exact branches (first :: second :: tail) bounded done

/-- Actual source selection removes operands without adding a boundary atom. -/
theorem column_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (origin : AtomCall call) (source : List NodeRef)
    (clear : Guard → Bool) (comparison : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ input ∈ inputs, Bounded source before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : column call clear comparison inputs before = .done result after) :
    Extension before after ∧ Bounded source after result := by
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
      obtain ⟨later, resultBounded⟩ := retained_bounded call checked origin source retained middle extension.facts extension.prepared
        (fun value member => bounded_grows source before middle extension value (bounded value (subset value member))) result after recursive
      exact ⟨extension.trans later, resultBounded⟩

/-- Each complete edge child uses only the common original atom list. -/
def EdgeBounded (source : List NodeRef) (state : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  EdgeResident state edge ∧ ∀ child ∈ edge.children, Within source child

/-- Actual edge readback retains the requested complete children and their atoms. -/
theorem edge_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (source : List NodeRef)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (bounded : ∀ value ∈ values, Bounded source state value) :
    Extension state (run (makeEdge symbol guard values) state).2 ∧
      EdgeBounded source (run (makeEdge symbol guard values) state).2 (run (makeEdge symbol guard values) state).1 := by
  have available : Values state values := fun value member => (bounded value member).1
  have verified := edge_verified symbol guard values state facts available
  refine ⟨⟨verified.facts, prepared.preserve (by intro key entry body depth ordinary stored; exact stored),
    verified.growth, verified.history⟩, verified.result _ _ rfl, ?_⟩
  rw [InternedShallowValues.makeEdge_children symbol guard values state facts.coherent facts.cached available]
  exact fun value member => (bounded value member).2

/-- Small groups process actual children without adding a boundary atom. -/
theorem small_bounded [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (origin : AtomCall call) (source : List NodeRef)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (bounded : EdgeBounded source before edge)
    (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) :
    Extension before after ∧ EdgeBounded source after result := by
  cases mapped : MergedColdMerge.map call edge.children before with
  | failed => simp only [small, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done values middle =>
      obtain ⟨extension, valuesBounded⟩ := map_bounded call checked origin source edge.children before facts prepared
        (fun value member => ⟨facts.cached.edges edge.entry.key edge bounded.1 value member, bounded.2 value member⟩) values middle mapped
      have equal : (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).1 = result ∧
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 = after := by
        simpa only [small, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨later, resultBounded⟩ := edge_bounded edge.entry.key.symbol edge.entry.key.constraint values source
        middle extension.facts extension.prepared valuesBounded
      exact ⟨extension.trans later, resultBounded⟩

/-- Positional source columns contain only atoms of the original grouped children. -/
theorem large_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (origin : AtomCall call) (source : List NodeRef)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ edge ∈ first :: rest, EdgeBounded source before edge)
    (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : large call clear comparison top first rest before = .done result after) :
    Extension before after ∧ EdgeBounded source after result := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have inputs : ∀ values ∈ columns, ∀ value ∈ values, Bounded source before value := by
    intro values member value included
    obtain ⟨row, rowMember, valueMember⟩ := MergedPhysicalGroupEdges.columns_member _ _ values member value included
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp rowMember
    exact ⟨facts.cached.edges edge.entry.key edge (bounded edge edgeMember).1 value valueMember,
      (bounded edge edgeMember).2 value valueMember⟩
  cases mapped : MergedColdMerge.map (column call clear comparison) columns before with
  | failed => simp only [large, columns, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done values middle =>
      obtain ⟨extension, related⟩ := map_valid (column call clear comparison)
        (fun state inputs => ∀ input ∈ inputs, Bounded source state input) (fun state _ result => Bounded source state result)
        (fun before after extension inputs bounded input member => bounded_grows source before after extension input (bounded input member))
        (fun before after extension _ result bounded => bounded_grows source before after extension result bounded)
        (fun inputs before result after facts prepared bounded done =>
          column_bounded call checked origin source clear comparison inputs before facts prepared bounded result after done)
        columns before facts prepared inputs values middle mapped
      have equal : (run (makeEdge first.entry.key.symbol top values) middle).1 = result ∧
          (run (makeEdge first.entry.key.symbol top values) middle).2 = after := by
        simpa only [large, columns, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨later, resultBounded⟩ := edge_bounded first.entry.key.symbol top values source middle
        extension.facts extension.prepared (EnumerationSoundness.all₂_outputs _ _ _ related)
      exact ⟨extension.trans later, resultBounded⟩

/-- Cache extension retains complete edges and their original boundary atoms. -/
theorem edgeBounded_grows (source : List NodeRef) (before after : State Symbol Guard)
    (extension : Extension before after) (edge : EdgeValue Symbol Guard)
    (bounded : EdgeBounded source before edge) : EdgeBounded source after edge :=
  ⟨edge_grows before after extension.growth edge bounded.1, bounded.2⟩

/-- Both actual group threshold branches retain the common original atom list. -/
theorem group_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (origin : AtomCall call) (source : List NodeRef)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ edge ∈ edges, EdgeBounded source before edge)
    (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : group call clear comparison top edges before = .done results after) :
    Extension before after ∧ ∀ edge ∈ results, EdgeBounded source after edge := by
  by_cases smallGroup : edges.length ≤ 4
  · obtain ⟨extension, related⟩ := map_valid (small call) (EdgeBounded source)
      (fun state _ result => EdgeBounded source state result) (edgeBounded_grows source)
      (fun before after extension _ result bounded => edgeBounded_grows source before after extension result bounded)
      (fun edge before result after facts prepared bounded done =>
        small_bounded call checked origin source edge before facts prepared bounded result after done)
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
            obtain ⟨extension, valid⟩ := large_bounded call checked origin source clear comparison top first rest
              before facts prepared bounded result final built
            exact ⟨extension, fun edge member => (List.mem_singleton.mp member).symm ▸ valid⟩

/-- Final source node normalization retains atoms of the actual grouped children. -/
theorem root_bounded [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid call) (origin : AtomCall call) (source : List NodeRef)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (groups : List (List (EdgeValue Symbol Guard)))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (bounded : ∀ group ∈ groups, ∀ edge ∈ group, EdgeBounded source before edge)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root call clear comparison top groups before = .done result after) : Within source result := by
  cases mapped : MergedColdMerge.map (group call clear comparison top) groups before with
  | failed => simp only [root, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done rows middle =>
      obtain ⟨extension, related⟩ := map_valid (group call clear comparison top)
        (fun state edges => ∀ edge ∈ edges, EdgeBounded source state edge)
        (fun state _ results => ∀ edge ∈ results, EdgeBounded source state edge)
        (fun before after extension edges valid edge member => edgeBounded_grows source before after extension edge (valid edge member))
        (fun before after extension _ edges valid edge member => edgeBounded_grows source before after extension edge (valid edge member))
        (fun edges before results after facts prepared bounded done =>
          group_bounded call checked origin source clear comparison top edges before facts prepared bounded results after done)
        groups before facts prepared bounded rows middle mapped
      have rowBounded := EnumerationSoundness.all₂_outputs _ _ _ related
      have allBounded : ∀ edge ∈ rows.flatten, EdgeBounded source middle edge := by
        intro edge member
        obtain ⟨row, present, included⟩ := List.mem_flatten.mp member
        exact rowBounded row present edge included
      have equal : (run (makeNode rows.flatten) middle).1 = result ∧
          (run (makeNode rows.flatten) middle).2 = after := by
        simpa only [root, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      intro atom present
      have original := makeNode_atom_origin rows.flatten middle extension.facts.coherent extension.facts.linked
        (fun edge member => (allBounded edge member).1) atom present
      obtain ⟨edge, member, child, included, occurrence⟩ := (edge_member _ atom).mp original
      exact (allBounded edge member).2 child included atom occurrence

/-- Every successful actual cold worker returns atoms from its unrestricted original input. -/
theorem worker_atoms [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat) :
    AtomCall (worker grouping clear top ordinary comparison) := by
  induction ordinary with
  | zero =>
      intro input before result after facts prepared available done
      cases input with
      | node entry edges depth free =>
          by_cases closed : free = []
          · simp [worker, closed] at done
          · simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done
            rcases done with ⟨rfl, rfl⟩
            exact fun _ member => member
      | empty | reference | union | mu =>
          simp only [worker, MergedColdMerge.pure, Result.done.injEq] at done
          rcases done with ⟨rfl, rfl⟩
          exact fun _ member => member
  | succ ordinary ih =>
      intro input before result after facts prepared available done
      cases input with
      | node entry edges depth free =>
          by_cases closed : free = []
          · subst free
            apply root_bounded (worker grouping clear top ordinary comparison)
              (worker_valid grouping correct clear top ordinary comparison) ih (atoms (.node entry edges depth []))
              clear comparison top (grouping edges) before facts prepared _ result after
              (by simpa only [worker, ↓reduceIte] using done)
            intro group groupMember edge edgeMember
            have member := (correct edges).partition.mem_iff.mp
              (List.mem_flatten.mpr ⟨group, groupMember, edgeMember⟩)
            refine ⟨resident_edges before facts.linked _ available.resident edge member, ?_⟩
            intro child included atom present
            exact child_atom (.node entry edges depth []) edge member child included atom present
          · simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done
            rcases done with ⟨rfl, rfl⟩
            exact fun _ member => member
      | empty | reference | union | mu =>
          simp only [worker, MergedColdMerge.pure, Result.done.injEq] at done
          rcases done with ⟨rfl, rfl⟩
          exact fun _ member => member

/-- The source executor uses the input-derived ordinary fuel without adding atoms. -/
theorem execute_atoms [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (comparison : Nat) (input : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Available before input)
    (done : execute grouping clear top comparison input before = .done result after) :
    ∀ atom ∈ atoms result, atom ∈ atoms input :=
  worker_atoms grouping correct clear top (height input) comparison input before result after facts prepared available done

end MicroCFTA.MergedPrefixAtoms
