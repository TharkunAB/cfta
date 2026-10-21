import MicroCFTA.MergedPhysicalGroupCalls
import MicroCFTA.EqualityLeafProjectionSetChildren

/-!
# Physical edge construction for alternative groups

The small branch retains the original symbol and guard. The large branch
uses the common group symbol and the unconstrained guard. Both branches
execute the child calls before actual edge interning and cache readback.
-/
namespace MicroCFTA.MergedPhysicalGroupEdges
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalUnionTransport MergedPhysicalGroupCalls Language

/-- A certificate belongs to one recursive child call, with its actual input and result caches. -/
def CallLaw [DecidableEq (EdgeKey Symbol Guard)]
    (call : Request → Work Symbol Guard (Value Symbol Guard))
    (operands : Request → List (Value Symbol Guard)) (request : Request)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool) : Prop :=
  ∀ state, Context state outputs → Values state (operands request) →
    let result := run (call request) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧ Covers state result.2 meaning (operands request) result.1

/-- Complete edge readback preserves the literal symbol, guard, and ordered child records. -/
theorem makeEdge_fields [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (available : Values state values) :
    let result := (run (makeEdge symbol guard values) state).1
    result.entry.key.symbol = symbol ∧ result.entry.key.constraint = guard ∧ result.children = values := by
  let key : EdgeKey Symbol Guard := ⟨symbol, values.map Value.referenceOf, guard⟩
  let identify := fun entry => EdgeValue.mk entry values
  have correct := edgeStep_correct key identify state facts.coherent.valid
  have coherent := edgeStep_coherent key identify state facts.coherent (fun _ same => ⟨rfl, same, rfl⟩)
  have fields := (coherent.edges key _ correct.2.2).2.1
  exact ⟨congrArg EdgeKey.symbol fields, congrArg EdgeKey.constraint fields,
    InternedShallowValues.makeEdge_children symbol guard values state facts.coherent facts.cached available⟩

/-- An earlier resident edge keeps every accepted term in a later prepared cache. -/
theorem edge_grow [DecidableEq (EdgeKey Symbol Guard)]
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context before outputs) (growth : Grows before after)
    (meaning : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard)
    (resident : EdgeResident before edge) (term : Term Symbol) (accepted : EdgeAccepts before meaning edge term) :
    EdgeAccepts after meaning edge term := by
  obtain ⟨terms, same, runs, guard⟩ := accepted
  exact ⟨terms, same, runs_grow before after outputs context growth meaning edge.children
    (context.facts.cached.edges edge.entry.key edge resident) terms runs, guard⟩

/-- Rebuild one small-group edge after the ordered recursive child calls. -/
def smallEdge (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edge : EdgeValue Symbol Guard) : Work Symbol Guard (EdgeValue Symbol Guard) :=
  (mapCalls merge edge.children).bind fun values => makeEdge edge.entry.key.symbol edge.entry.key.constraint values

/-- The actual source setChildren call takes its equal-arity direct interning branch. -/
theorem smallEdge_setChildren [DecidableEq (EdgeKey Symbol Guard)]
    (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (edge : EdgeValue Symbol Guard)
    (state : InternedConstructorTemplates.State Symbol Guard) :
    run ((mapCalls merge edge.children).bind (EqualityLeafProjectionSetChildren.setChildren checked edge)) state =
      run (smallEdge merge edge) state := by
  simp only [smallEdge, run_bind]
  rw [EqualityLeafProjectionSetChildren.same_arity checked edge _ (mapCalls_length merge edge.children state)]

/-- A small-group edge retains its full guard and includes the original edge language. -/
theorem smallEdge_correct [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (edge : EdgeValue Symbol Guard)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (certified : ∀ child ∈ edge.children, CallLaw merge (fun value => [value]) child outputs meaning)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (resident : EdgeResident state edge) :
    let result := run (smallEdge merge edge) state
    Context result.2 outputs ∧ EdgeResident result.2 result.1 ∧
      result.1.entry.key.symbol = edge.entry.key.symbol ∧ result.1.entry.key.constraint = edge.entry.key.constraint ∧
      result.1.children.length = edge.children.length ∧
      ∀ term, EdgeAccepts state meaning edge term → EdgeAccepts result.2 meaning result.1 term := by
  let children := run (mapCalls merge edge.children) state
  have childInputs : ∀ child ∈ edge.children, Values state [child] := by
    intro child member value included
    rw [List.mem_singleton.mp included]
    exact context.facts.cached.edges edge.entry.key edge resident child member
  have childChecked := mapCalls_correct merge (fun value => [value]) edge.children outputs meaning certified state context childInputs
  have edgeChecked := childChecked.1.makeEdge children.2 outputs edge.entry.key.symbol edge.entry.key.constraint children.1 childChecked.2.1
  have fields := makeEdge_fields children.2 childChecked.1.facts edge.entry.key.symbol edge.entry.key.constraint children.1 childChecked.2.1
  have growth := (InternedConstructorTemplates.run_correct
    (makeEdge edge.entry.key.symbol edge.entry.key.constraint children.1) children.2 childChecked.1.facts.coherent.valid).2
  simp only [smallEdge, run_bind]
  refine ⟨edgeChecked.1, edgeChecked.2, fields.1, fields.2.1, ?_, ?_⟩
  · rw [fields.2.2]
    exact mapCalls_length merge edge.children state
  · intro term accepted
    obtain ⟨terms, same, runs, guard⟩ := accepted
    refine ⟨terms, by rw [fields.1]; exact same, ?_, by rw [fields.2.1]; exact guard⟩
    rw [fields.2.2]
    apply runs_grow children.2 _ outputs childChecked.1 growth meaning children.1 childChecked.2.1 terms
    apply covers_runs state children.2 meaning (fun value => [value]) edge.children children.1 terms childChecked.2.2
    exact runs.imp (fun value term accepted => ⟨value, List.mem_singleton_self _, accepted⟩)

/-- Physical source group membership requires one symbol and one child arity. -/
def SameKey (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ first ∈ edges, ∀ second ∈ edges,
    first.entry.key.symbol = second.entry.key.symbol ∧ first.children.length = second.children.length

/-- Construct the large-group edge after the ordered column calls. -/
def largeEdge (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) : Work Symbol Guard (EdgeValue Symbol Guard) :=
  (mapCalls mergeUnion (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length)).bind
    fun values => makeEdge first.entry.key.symbol top values

/-- Every value in a child column belongs to an original row. -/
theorem columns_member (rows : List (List A)) (arity : Nat) (column : List A)
    (included : column ∈ MergedAlternativesGroups.columns rows arity) (value : A) (member : value ∈ column) :
    ∃ row ∈ rows, value ∈ row := by
  induction arity generalizing rows with
  | zero => simp [MergedAlternativesGroups.columns] at included
  | succ arity ih =>
      rcases List.mem_cons.mp included with same | later
      · rw [same] at member
        obtain ⟨row, present, selected⟩ := List.mem_filterMap.mp member
        refine ⟨row, present, ?_⟩
        cases row <;> simp_all
      · obtain ⟨tail, present, member⟩ := ih _ later
        obtain ⟨row, original, rfl⟩ := List.mem_map.mp present
        exact ⟨row, original, List.mem_of_mem_tail member⟩

/-- The modeled transpose has exactly the common source arity. -/
theorem columns_length (rows : List (List A)) (arity : Nat) :
    (MergedAlternativesGroups.columns rows arity).length = arity := by
  induction arity generalizing rows with
  | zero => rfl
  | succ arity ih => simp only [MergedAlternativesGroups.columns, List.length_cons, ih]

/-- A large-group edge includes every source row through actual column and edge effects. -/
theorem largeEdge_correct [DecidableEq (EdgeKey Symbol Guard)]
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool) (clear : ∀ term, meaning top term = true)
    (certified : ∀ column ∈ MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length,
      CallLaw mergeUnion id column outputs meaning)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (resident : Edges state (first :: rest)) (sameKey : SameKey (first :: rest)) :
    let result := run (largeEdge mergeUnion top first rest) state
    Context result.2 outputs ∧ EdgeResident result.2 result.1 ∧
      result.1.entry.key.symbol = first.entry.key.symbol ∧ result.1.entry.key.constraint = top ∧
      result.1.children.length = first.children.length ∧
      ∀ original ∈ first :: rest, ∀ term, EdgeAccepts state meaning original term → EdgeAccepts result.2 meaning result.1 term := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  let children := run (mapCalls mergeUnion columns) state
  have inputs : ∀ column ∈ columns, Values state (id column) := by
    intro column included value member
    obtain ⟨row, present, member⟩ := columns_member _ _ column included value member
    obtain ⟨edge, original, rfl⟩ := List.mem_map.mp present
    exact context.facts.cached.edges edge.entry.key edge (resident edge original) value member
  have childChecked := mapCalls_correct mergeUnion id columns outputs meaning certified state context inputs
  have edgeChecked := childChecked.1.makeEdge children.2 outputs first.entry.key.symbol top children.1 childChecked.2.1
  have fields := makeEdge_fields children.2 childChecked.1.facts first.entry.key.symbol top children.1 childChecked.2.1
  have growth := (InternedConstructorTemplates.run_correct
    (makeEdge first.entry.key.symbol top children.1) children.2 childChecked.1.facts.coherent.valid).2
  simp only [largeEdge, run_bind]
  refine ⟨edgeChecked.1, edgeChecked.2, fields.1, fields.2.1, ?_, ?_⟩
  · rw [fields.2.2, mapCalls_length]
    exact columns_length _ _
  · intro original member term accepted
    obtain ⟨terms, same, runs, _⟩ := accepted
    obtain ⟨symbol, arity⟩ := sameKey original member first List.mem_cons_self
    refine ⟨terms, by rw [fields.1, ← symbol]; exact same, ?_, by rw [fields.2.1]; exact clear term⟩
    rw [fields.2.2]
    apply runs_grow children.2 _ outputs childChecked.1 growth meaning children.1 childChecked.2.1 terms
    apply covers_runs state children.2 meaning id columns children.1 terms childChecked.2.2
    have covered := MergedAlternativesGroups.columns_cover (EpsilonUnion.Accepts (graph state meaning))
      ((first :: rest).map EdgeValue.children) original.children terms (List.mem_map.mpr ⟨original, member, rfl⟩) runs
    simpa only [arity, columns, id] using covered

end MicroCFTA.MergedPhysicalGroupEdges
