import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedGuardedLanguage

/-!
# A canonical closed opaque union with two accepted arities

The actual constructor builds union[a[], mu X.(a[] | a[X])] from empty
caches. The recursive member prevents the ordinary-union fast path.
The witness has both a nullary accepted term and a unary accepted term.
It does not establish an original synthesis history or a caller Context.
-/
namespace MicroCFTA.InternedOpaqueUnionWitness
set_option pp.maxSteps 800
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedProbeProvenance InternedFreshProbeKeys
variable {Symbol Guard : Type}

private def leafEdge (symbol : Symbol) (guard : Guard) : EdgeValue Symbol Guard :=
  .mk ⟨0, ⟨symbol, [], guard⟩⟩ []

/-- The first ordinary member has one nullary edge. -/
def leaf (symbol : Symbol) (guard : Guard) : Value Symbol Guard :=
  .node ⟨0, .node [0]⟩ [leafEdge symbol guard] 0 []

private def body (symbol : Symbol) (guard : Guard) (name : Reference)
    (edgeIdentity nodeIdentity : Nat) : Value Symbol Guard :=
  .node ⟨nodeIdentity, .node [0, edgeIdentity]⟩
    [leafEdge symbol guard, .mk ⟨edgeIdentity, ⟨symbol, [.ref name], guard⟩⟩ [.reference name]]
    0 [name]

private def recursiveEntry : Interned NodeKey :=
  ⟨3, .mu ⟨.node 1, .node 2⟩⟩

/-- The actual stored recursive member retains its body and both completed probes. -/
def recursive (symbol : Symbol) (guard : Guard) : Value Symbol Guard :=
  .mu recursiveEntry (body symbol guard (.interned 3) 3 4)
    (body symbol guard .depth 1 1) (body symbol guard (.uninterned 0) 2 2)

private def rootEntry : Interned NodeKey := ⟨5, .union [.node 0, .mu 3]⟩

/-- This union retains one ordinary member and one genuine recursive member. -/
def value (symbol : Symbol) (guard : Guard) : Value Symbol Guard :=
  .union rootEntry [leaf symbol guard, recursive symbol guard] 1 []

/-- The finite source expression performs the actual ordinary and Mu construction. -/
def expression (symbol : Symbol) (guard : Guard) : Syntax Symbol Guard :=
  .union [.node [.mk symbol guard []],
    .binder true (.node [.mk symbol guard [], .mk symbol guard [.var 0]])]

/-- The completed value has no free reference. -/
theorem closed (symbol : Symbol) (guard : Guard) : (value symbol guard).free = [] := rfl

section Computation
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Execute the actual fresh ordinary constructor from empty caches. -/
def construction (symbol : Symbol) (guard : Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  InternedFreshOrdinaryConstruction.build (expression symbol guard) [] empty

/-- Read the exact constructor heap from that same execution. -/
def heap (symbol : Symbol) (guard : Guard) : InternedConstructorTemplates.State Symbol Guard :=
  (construction symbol guard).state

section Replay
attribute [local simp]
  construction expression heap value leaf leafEdge body recursive recursiveEntry rootEntry
  InternedFreshOrdinaryConstruction.build InternedFreshOrdinaryConstruction.buildMany
  InternedFreshOrdinaryConstruction.buildEdges InternedFreshOrdinaryConstruction.ordinaryLevel
  InternedFreshOrdinaryConstruction.freeBound
  InternedNestedConstruction.Outcome.bind InternedNestedConstruction.work
  InternedNestedConstruction.request InternedNestedConstruction.finish InternedNestedConstruction.Outcome.state
  InternedConstructorTemplates.run InternedConstructorTemplates.Work.bind
  makeEdge makeUnion edgeStep nodeStep identifyNode
  ordinaryEdges distinctNodes unionMembers surviving canonicalEdges
  maximumDepth childFree canonicalFree Value.depth Value.free Value.referenceOf
  EdgeValue.children EdgeValue.entry
  muKey withoutSelfReference cleanup
  Cache.intern Cache.reserve Cache.install Cache.keepFirst Cache.put Cache.emptyState empty
  EnumerationBuilderCaches.canonicalIds List.find?_cons List.eraseDups_cons List.mergeSort List.merge

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem node_single (key : EdgeKey Symbol Guard) :
    makeNode [.mk ⟨0, key⟩ []] =
      .node (.node [0]) (fun entry => .node entry [.mk ⟨0, key⟩ []] 0 []) InternedConstructorTemplates.Work.pure := by
  simp only [makeNode]
  simp
  funext entry
  simp [InternedConstructorTemplates.identifyNode]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem node_pair (first second : EdgeKey Symbol Guard) (name : Reference) (index : Nat) :
    makeNode [.mk ⟨0, first⟩ [], .mk ⟨index + 1, second⟩ [.reference name]] =
      .node (.node [0, index + 1])
        (fun entry => .node entry
          [.mk ⟨0, first⟩ [], .mk ⟨index + 1, second⟩ [.reference name]] 0 [name]) InternedConstructorTemplates.Work.pure := by
  simp only [makeNode]
  simp
  funext entry
  simp [InternedConstructorTemplates.identifyNode]

attribute [local simp] node_single node_pair

/-- The completed execution returns this literal recursive union and the same constructor heap. -/
theorem built (symbol : Symbol) (guard : Guard) :
    construction symbol guard = .done (value symbol guard) (heap symbol guard) := by
  simp
  <;> rfl
end Replay

/-- All actual constructor facts hold at the same returned heap. -/
theorem facts (symbol : Symbol) (guard : Guard) : InternedNestedFacts.Facts (heap symbol guard) :=
  (InternedFreshOrdinaryFacts.build_verified (expression symbol guard) [] empty
    InternedNestedFacts.empty_facts (by intro child member; cases member)).facts

/-- Availability is derived from the actual completed constructor, including its Mu children. -/
theorem available (symbol : Symbol) (guard : Guard) : Available (heap symbol guard) (value symbol guard) :=
  (InternedFreshOrdinaryFacts.build_verified (expression symbol guard) [] empty
    InternedNestedFacts.empty_facts (by intro child member; cases member)).result
      (value symbol guard) (heap symbol guard) (built symbol guard)

/-- The returned cache records satisfy canonical coherence. -/
theorem coherent (symbol : Symbol) (guard : Guard) : InternedRecordCoherence.Coherent (heap symbol guard) :=
  (facts symbol guard).coherent

/-- Canonical readback retains the issued union identity, its entry and its complete payload. -/
theorem readback (symbol : Symbol) (guard : Guard) :
    (heap symbol guard).nodes.issued 5 = some rootEntry.key ∧
    (heap symbol guard).nodes.table rootEntry.key = some rootEntry ∧
    (heap symbol guard).nodeRecords rootEntry.key = some (value symbol guard) := by
  have resident := (available symbol guard).resident
  have canonical := resident_entry (heap symbol guard) (coherent symbol guard)
    (value symbol guard) resident rootEntry rfl
  exact ⟨((coherent symbol guard).valid.2.2 _ _ canonical).2, canonical, resident rootEntry rfl⟩

end Computation

section Language
open Language InternedGuardedLanguage

private theorem leaf_accepted (symbol : Symbol) (guard : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (accepted : holds guard (.node symbol []) = true) :
    meaning holds ambient (leaf symbol guard) (.node symbol []) := by
  rw [leaf, meaning]
  refine ⟨⟨leafEdge symbol guard, List.mem_cons_self⟩, ?_⟩
  rw [leafEdge, edgeMeaning]
  exact ⟨[], rfl, by simp only [forest], accepted⟩

private theorem body_leaf_accepted (symbol : Symbol) (guard : Guard)
    (name : Reference) (edgeIdentity nodeIdentity : Nat)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (accepted : holds guard (.node symbol []) = true) :
    meaning holds ambient (body symbol guard name edgeIdentity nodeIdentity) (.node symbol []) := by
  rw [body, meaning]
  refine ⟨⟨leafEdge symbol guard, List.mem_cons_self⟩, ?_⟩
  rw [leafEdge, edgeMeaning]
  exact ⟨[], rfl, by simp only [forest], accepted⟩

private theorem body_unary_accepted (symbol : Symbol) (guard : Guard)
    (name : Reference) (edgeIdentity nodeIdentity : Nat)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (child : ambient name (.node symbol []))
    (accepted : holds guard (.node symbol [.node symbol []]) = true) :
    meaning holds ambient (body symbol guard name edgeIdentity nodeIdentity)
      (.node symbol [.node symbol []]) := by
  rw [body, meaning]
  refine ⟨⟨.mk ⟨edgeIdentity, ⟨symbol, [.ref name], guard⟩⟩ [.reference name],
    List.mem_cons_of_mem _ List.mem_cons_self⟩, ?_⟩
  rw [edgeMeaning]
  refine ⟨[.node symbol []], rfl, ?_, accepted⟩
  simpa only [forest, meaning] using And.intro child True.intro

/-- The actual opaque union accepts its nullary member under the literal edge guard. -/
theorem nullary_accepted (symbol : Symbol) (guard : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (accepted : holds guard (.node symbol []) = true) :
    meaning holds ambient (value symbol guard) (.node symbol []) := by
  rw [value, meaning]
  exact ⟨⟨leaf symbol guard, List.mem_cons_self⟩, leaf_accepted symbol guard holds ambient accepted⟩

/-- The recursive alternative also accepts a unary term with a valid child-zero path. -/
theorem unary_accepted (symbol : Symbol) (guard : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (base : holds guard (.node symbol []) = true)
    (step : holds guard (.node symbol [.node symbol []]) = true) :
    meaning holds ambient (value symbol guard) (.node symbol [.node symbol []]) := by
  have baseMember : meaning holds ambient (recursive symbol guard) (.node symbol []) := by
    rw [recursive, mu_unfold]
    exact body_leaf_accepted symbol guard (.interned 3) 3 4 holds _ base
  have recursiveMember : meaning holds ambient (recursive symbol guard) (.node symbol [.node symbol []]) := by
    rw [recursive, mu_unfold]
    refine body_unary_accepted symbol guard (.interned 3) 3 4 holds _ ?_ step
    simpa only [InternedGuardedLanguage.bind, recursiveEntry, recursive, ↓reduceIte] using baseMember
  rw [value, meaning]
  exact ⟨⟨recursive symbol guard, List.mem_cons_of_mem _ List.mem_cons_self⟩, recursiveMember⟩
end Language

end MicroCFTA.InternedOpaqueUnionWitness
