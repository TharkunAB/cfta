import MicroCFTA.SourceRecursiveIntersectionMaybeMuCompletion

/-!
# Semantic heaps through actual recursive intersection effects

The actual emitted edge, node, union, and optional-binder operations retain
normalization and all decoded recursive heaps. Input availability remains
explicit. Arbitrary constructor work has no preservation claim.
-/
namespace MicroCFTA.SourceRecursiveIntersectionSemanticHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshOrdinaryContext
open InternedStoredMuOrigins (Normal)

/-- The constructor heap retains normalization and all three decoded recursive observations. -/
def SemanticHeap (state : State Symbol Guard) : Prop :=
  Context state [] ∧ InternedFreshOrdinaryDepthHeap.Heap state

/-- Empty source caches satisfy every semantic heap invariant. -/
theorem empty_heap : SemanticHeap (empty (Symbol := Symbol) (Guard := Guard)) :=
  ⟨empty_context, InternedFreshOrdinaryDepthHeap.empty_heap⟩

/-- Available lexical inputs can be added to the same complete semantic heap. -/
theorem context (state : State Symbol Guard) (semantic : SemanticHeap state)
    (environment : List (Value Symbol Guard)) (available : ∀ value ∈ environment, Available state value) :
    Context state environment :=
  ⟨semantic.1.normal, available, semantic.1.profiles, semantic.1.freeNames⟩

/-- An ordinary effect retains decoded heaps when it adds no recursive record. -/
theorem preserve (before after : State Symbol Guard) (semantic : SemanticHeap before) (normal : Normal after)
    (old : InternedShallowHeap.NoNewMu before after) : SemanticHeap after :=
  ⟨⟨normal, (by intro value member; cases member),
      InternedFreshOrdinaryProfileHeap.preserve before after semantic.1.profiles old,
      InternedFreshOrdinaryFreeHeap.preserve before after semantic.1.freeNames old⟩,
    InternedFreshOrdinaryDepthHeap.preserve before after semantic.2 old⟩

/-- Actual edge construction retains the full semantic heap from available children. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (semantic : SemanticHeap state)
    (available : ∀ value ∈ values, Available state value) : SemanticHeap (run (makeEdge symbol guard values) state).2 :=
  preserve state _ semantic (InternedNestedMuOrigins.edge_normal symbol guard values state semantic.1.normal available)
    (InternedShallowHeap.noNewMu_refl state)

/-- Actual node construction retains all semantic heaps from its resident ordered edges. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (semantic : SemanticHeap state)
    (resident : ∀ edge ∈ edges, InternedEdgeResidency.EdgeResident state edge) :
    SemanticHeap (run (makeNode edges) state).2 := by
  have normal := semantic.1.normal
  have checked := InternedNestedFacts.node_verified edges state normal.facts resident
  apply preserve state _ semantic ?_ (InternedShallowHeap.makeNode_noNewMu edges state)
  exact ⟨checked.facts,
    InternedLiveEdges.makeNode_live edges state normal.live,
    InternedUnionNormalForm.makeNode_flat edges state normal.flat,
    InternedNonemptyRecords.makeNode_nonempty edges state normal.proper,
    InternedUnionNonemptyMembers.makeNode_membersNonempty edges state normal.members⟩

/-- Actual union construction retains all semantic heaps from its available ordered operands. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (semantic : SemanticHeap state)
    (available : ∀ value ∈ values, Available state value) : SemanticHeap (run (makeUnion values) state).2 := by
  have normal := semantic.1.normal
  have checked := InternedNestedFacts.union_verified values state normal.facts available
  apply preserve state _ semantic ?_ (InternedShallowHeap.makeUnion_noNewMu values state)
  exact ⟨checked.facts,
    InternedLiveEdges.makeUnion_live values state normal.live,
    InternedUnionNormalForm.makeUnion_flat values state normal.flat available,
    InternedNonemptyRecords.makeUnion_nonempty values state normal.proper,
    InternedUnionNonemptyMembers.makeUnion_membersNonempty values state normal.members available⟩

/-- Actual optional binders retain the semantic heaps for every outcome and arbitrary available body. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (available : Available state body) :
    SemanticHeap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state :=
  SourceRecursiveIntersectionMaybeMu.semantic_context pair body state semantic.1 available semantic.2

/-- Arbitrary repaired source execution retains the full semantic heap without assuming completion. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (semantic : SemanticHeap state)
    (available : ∀ value ∈ environment, Available state value) :
    SemanticHeap (InternedFreshOrdinaryConstruction.build expression environment state).state := by
  have initial := context state semantic environment available
  have after := initial.build expression
  exact ⟨⟨after.normal, (by intro value member; cases member), after.profiles, after.freeNames⟩,
    (InternedRecordDepthExecution.build_depth expression environment state initial semantic.2).heap⟩

end MicroCFTA.SourceRecursiveIntersectionSemanticHeap
