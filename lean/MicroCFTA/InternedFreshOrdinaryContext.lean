import MicroCFTA.InternedFreshOrdinarySourceFreeNames

/-!
# Complete semantic contexts for repaired constructor execution

A context retains normalization, available lexical values, and both semantic
heaps. Actual execution preserves the context even when it reaches a pending
request. Complete origins can therefore retain their earlier semantic evidence.
-/
namespace MicroCFTA.InternedFreshOrdinaryContext
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal empty_normal reserve_normal)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryNormal
open InternedBinderProtocol (Reference NodeKey)

/-- Every input value and both decoded recursive heaps are valid at this source point. -/
structure Context (state : State Symbol Guard) (environment : List (Value Symbol Guard)) : Prop where
  normal : Normal state
  inputs : Values state environment
  profiles : InternedFreshOrdinaryProfileHeap.Heap state
  freeNames : InternedFreshOrdinaryFreeHeap.Heap state

/-- The initial source context has no lexical inputs or stored recursive records. -/
theorem empty_context : Context (empty (Symbol := Symbol) (Guard := Guard)) [] :=
  ⟨empty_normal, (by intro value member; cases member),
    InternedFreshOrdinaryProfileHeap.empty_heap, InternedFreshOrdinaryFreeHeap.empty_heap⟩

/-- A completed or pending expression retains its original lexical values and both heaps. -/
theorem Context.build [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expression : Syntax Symbol Guard) : Context (build expression environment state).state environment :=
  ⟨build_normal expression environment state context.normal context.inputs,
    fun value member => (build_verified expression environment state context.normal.facts context.inputs).available value (context.inputs value member),
    (InternedFreshOrdinaryProfiles.build_profile expression environment state context.normal context.inputs context.profiles).heap,
    (InternedFreshOrdinaryFreeNames.build_free expression environment state context.normal context.inputs context.freeNames context.profiles).heap⟩

/-- Ordered child construction retains the original semantic context. -/
theorem Context.many [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expressions : List (Syntax Symbol Guard)) : Context (buildMany expressions environment state).state environment :=
  ⟨buildMany_normal expressions environment state context.normal context.inputs,
    fun value member => (buildMany_verified expressions environment state context.normal.facts context.inputs).available value (context.inputs value member),
    (InternedFreshOrdinaryProfiles.buildMany_profile expressions environment state context.normal context.inputs context.profiles).heap,
    (InternedFreshOrdinaryFreeNames.buildMany_free expressions environment state context.normal context.inputs context.freeNames context.profiles).heap⟩

/-- Ordered edge construction retains the original semantic context. -/
theorem Context.edges [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expressions : List (EdgeSyntax Symbol Guard)) : Context (buildEdges expressions environment state).state environment :=
  ⟨buildEdges_normal expressions environment state context.normal context.inputs,
    fun value member => (buildEdges_verified expressions environment state context.normal.facts context.inputs).available value (context.inputs value member),
    (InternedFreshOrdinaryProfiles.buildEdges_profile expressions environment state context.normal context.inputs context.profiles).heap,
    (InternedFreshOrdinaryFreeNames.buildEdges_free expressions environment state context.normal context.inputs context.freeNames context.profiles).heap⟩

/-- Adding an available literal argument changes neither semantic heap. -/
theorem Context.local (context : Context state environment) (name : Reference)
    (available : Available state (.reference name)) : Context state (.reference name :: environment) := by
  refine ⟨context.normal, ?_, context.profiles, context.freeNames⟩
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact available
  · exact context.inputs value member

/-- An actual normalized callback retains the original semantic context. -/
theorem Context.callback [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (expression : Syntax Symbol Guard) (name : Reference) (available : Available state (.reference name)) :
    Context (callback expression environment name state).state environment := by
  have inputs := (context.local name available).inputs
  exact ⟨callback_normal expression environment name state context.normal inputs,
    fun value member => (callback_verified expression environment name state context.normal.facts inputs).available value (context.inputs value member),
    InternedFreshOrdinarySourceFreeNames.callback_profile_heap expression environment name state context.normal inputs context.profiles,
    (InternedFreshOrdinarySourceFreeNames.callback_checked expression environment name state context.normal inputs context.freeNames context.profiles).heap⟩

/-- Ordinary edge allocation adds no recursive payload and retains all captured values. -/
theorem Context.edge [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (inputs : Values state values) :
    Context (run (makeEdge symbol guard values) state).2 environment :=
  ⟨InternedNestedMuOrigins.edge_normal symbol guard values state context.normal inputs,
    fun value member => (InternedNestedFacts.edge_verified symbol guard values state context.normal.facts inputs).available value (context.inputs value member),
    context.profiles, context.freeNames⟩

/-- A fresh reservation preserves the complete semantic context before its body callback. -/
theorem Context.reserve (context : Context state environment) (key : NodeKey) :
    Context {state with nodes := (Cache.intern state.nodes key).2} environment := by
  have growth : Grows state {state with nodes := (Cache.intern state.nodes key).2} :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := InternedFreshProbeKeys.intern_issued_extends state.nodes key context.normal.facts.coherent.valid.2
  exact ⟨reserve_normal key state context.normal,
    fun value member => (context.inputs value member).grows _ _ growth history, context.profiles, context.freeNames⟩

end MicroCFTA.InternedFreshOrdinaryContext
