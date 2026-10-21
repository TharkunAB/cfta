import MicroCFTA.MergedPhysicalGroupColumnWorker

/-!
# Physical sequencing of all ordinary-root groups

The HashMap group order is an explicit parameter. Each group has one source
symbol and arity. The groups contain exactly the original canonical rows.
Actual child, edge, and parent effects determine the returned cache.
-/
namespace MicroCFTA.MergedPhysicalGroupRoot
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges MergedOrdinaryHeight Language

/-- Separate local certificates for the group's child and column requests. -/
structure Calls [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (outputs : List (Value Symbol Guard))
    (meaning : Guard → Term Symbol → Bool) : Prop where
  children : ∀ edge ∈ edges, ∀ child ∈ edge.children, CallLaw merge (fun value => [value]) child outputs meaning
  columns : ∀ first rest, edges = first :: rest →
    ∀ column ∈ MergedAlternativesGroups.columns (edges.map EdgeValue.children) first.children.length,
      CallLaw mergeUnion id column outputs meaning

/-- Source groups preserve the canonical row order within each complete symbol/arity class. -/
structure Grouping [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard))
    (input : List (List (EdgeValue Symbol Guard))) : Prop where
  partition : input.flatten.Perm edges
  exact : ∀ group ∈ input, ∃ first rest, group = first :: rest ∧
    group = edges.filter (fun edge => decide (edge.entry.key.symbol = first.entry.key.symbol ∧
      edge.children.length = first.children.length))

/-- Exact source grouping derives the homogeneous key premise of the physical group proof. -/
theorem Grouping.keys [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard))
    (input : List (List (EdgeValue Symbol Guard))) (grouping : Grouping edges input) :
    ∀ group ∈ input, SameKey group := by
  intro group included left leftIn right rightIn
  obtain ⟨first, rest, _, exactGroup⟩ := grouping.exact group included
  rw [exactGroup] at leftIn rightIn
  have leftKey := of_decide_eq_true (List.mem_filter.mp leftIn).2
  have rightKey := of_decide_eq_true (List.mem_filter.mp rightIn).2
  exact ⟨leftKey.1.trans rightKey.1.symm, leftKey.2.trans rightKey.2.symm⟩

/-- Sequence the source group order and concatenate the actual edge results. -/
def groups (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard)) (top : Guard) :
    List (List (EdgeValue Symbol Guard)) → Work Symbol Guard (List (EdgeValue Symbol Guard))
  | [] => .pure []
  | first :: rest => (MergedPhysicalGroup.group merge mergeUnion top first).bind fun edges =>
      (groups merge mergeUnion top rest).bind fun later => .pure (edges ++ later)

/-- Every original row is covered after all group computations finish. -/
theorem groups_correct [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (input : List (List (EdgeValue Symbol Guard)))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool) (clear : ∀ term, meaning top term = true)
    (calls : ∀ edges ∈ input, Calls merge mergeUnion edges outputs meaning)
    (keys : ∀ edges ∈ input, SameKey edges)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (resident : Edges state input.flatten) :
    let result := run (groups merge mergeUnion top input) state
    Context result.2 outputs ∧ Edges result.2 result.1 ∧
      ∀ original ∈ input.flatten, ∀ term, EdgeAccepts state meaning original term →
        ∃ edge ∈ result.1, EdgeAccepts result.2 meaning edge term := by
  induction input generalizing state with
  | nil => exact ⟨context, by simp [Edges, groups, run], by simp⟩
  | cons first rest ih =>
      let head := run (MergedPhysicalGroup.group merge mergeUnion top first) state
      let tail := run (groups merge mergeUnion top rest) head.2
      have firstCalls := calls first List.mem_cons_self
      have firstChecked := MergedPhysicalGroup.group_correct merge mergeUnion top first outputs meaning clear
        firstCalls.children firstCalls.columns state context
        (fun edge member => resident edge (by simp [member])) (keys first List.mem_cons_self)
      have headGrowth := (InternedConstructorTemplates.run_correct
        (MergedPhysicalGroup.group merge mergeUnion top first) state context.facts.coherent.valid).2
      have restChecked := ih (fun edges member => calls edges (List.mem_cons_of_mem _ member))
        (fun edges member => keys edges (List.mem_cons_of_mem _ member)) head.2 firstChecked.1
        (fun edge member => edge_grows state head.2 headGrowth edge (resident edge (by simp [member])))
      have tailGrowth := (InternedConstructorTemplates.run_correct
        (groups merge mergeUnion top rest) head.2 firstChecked.1.facts.coherent.valid).2
      simp only [groups, run_bind, run]
      refine ⟨restChecked.1, ?_, ?_⟩
      · intro edge member
        rcases List.mem_append.mp member with member | member
        · exact edge_grows head.2 tail.2 tailGrowth edge (firstChecked.2.1 edge member)
        · exact restChecked.2.1 edge member
      · intro original member term accepted
        rcases List.mem_append.mp member with member | member
        · obtain ⟨edge, included, _, _, _, covers⟩ := firstChecked.2.2.2 original member
          exact ⟨edge, List.mem_append_left _ included,
            edge_grow head.2 tail.2 outputs firstChecked.1 tailGrowth meaning edge (firstChecked.2.1 edge included) term (covers term accepted)⟩
        · obtain ⟨edge, included, accepted⟩ := restChecked.2.2 original member term
            (edge_grow state head.2 outputs context headGrowth meaning original (resident original (by simp [member])) term accepted)
          exact ⟨edge, List.mem_append_right _ included, accepted⟩

/-- Construct the ordinary root from the actual complete group results. -/
def build (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (input : List (List (EdgeValue Symbol Guard))) : Work Symbol Guard (Value Symbol Guard) :=
  (groups merge mergeUnion top input).bind makeNode

/-- Actual ordinary-root construction covers the source root's finite language. -/
theorem build_covers [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (input : List (List (EdgeValue Symbol Guard)))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (partition : ∀ edge, edge ∈ input.flatten ↔ edge ∈ edges)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool) (clear : ∀ term, meaning top term = true)
    (calls : ∀ edges ∈ input, Calls merge mergeUnion edges outputs meaning)
    (keys : ∀ edges ∈ input, SameKey edges)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (available : Available state (.node entry edges depth free)) :
    let result := run (build merge mergeUnion top input) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧
      ∀ term, EpsilonUnion.Accepts (graph state meaning) (.node entry edges depth free) term →
        EpsilonUnion.Accepts (graph result.2 meaning) result.1 term := by
  let merged := run (groups merge mergeUnion top input) state
  have resident : Edges state input.flatten := fun edge member =>
    resident_edges state context.facts.linked _ available.resident edge ((partition edge).mp member)
  have checked := groups_correct merge mergeUnion top input outputs meaning clear calls keys state context resident
  have built := checked.1.makeNode merged.2 outputs merged.1 checked.2.1
  have growth := (InternedConstructorTemplates.run_correct (makeNode merged.1) merged.2 checked.1.facts.coherent.valid).2
  simp only [build, run_bind]
  refine ⟨built.1, built.2, ?_⟩
  intro term accepted
  obtain ⟨original, member, accepted⟩ := (node_exact state meaning entry edges depth free term).mp accepted
  obtain ⟨edge, included, accepted⟩ := checked.2.2 original ((partition original).mpr member) term accepted
  exact (makeNode_exact merged.2 _ checked.1.facts merged.1 checked.2.1 meaning term).mpr
    ⟨edge, included, edge_grow merged.2 _ outputs checked.1 growth meaning edge (checked.2.1 edge included) term accepted⟩

/-- The source's complete symbol/arity grouping specializes the ordinary-root coverage theorem. -/
theorem grouped_root_covers [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (input : List (List (EdgeValue Symbol Guard)))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (grouping : Grouping edges input)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool) (clear : ∀ term, meaning top term = true)
    (calls : ∀ edges ∈ input, Calls merge mergeUnion edges outputs meaning)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (available : Available state (.node entry edges depth free)) :
    let result := run (build merge mergeUnion top input) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧
      ∀ term, EpsilonUnion.Accepts (graph state meaning) (.node entry edges depth free) term →
        EpsilonUnion.Accepts (graph result.2 meaning) result.1 term :=
  build_covers merge mergeUnion top input entry edges depth free (fun _ => grouping.partition.mem_iff)
    outputs meaning clear calls (grouping.keys edges input) state context available

/-- A parent-height induction hypothesis supplies every direct child call in any of its groups. -/
theorem children_below [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (smaller : ∀ value, height value < height (.node entry edges depth free) → CallLaw merge (fun value => [value]) value outputs meaning)
    (group : List (EdgeValue Symbol Guard)) (subset : ∀ edge ∈ group, edge ∈ edges) :
    ∀ edge ∈ group, ∀ child ∈ edge.children, CallLaw merge (fun value => [value]) child outputs meaning := by
  intro edge member child included
  exact smaller child (child_lt entry edges depth free edge (subset edge member) child included)

end MicroCFTA.MergedPhysicalGroupRoot
