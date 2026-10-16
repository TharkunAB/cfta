import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequired
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite

/-!
# Exact ordinary profiles through required-path execution

Selected children retain the original uniform row and arity limits.
Rejected rows disappear before child traversal. Retained rows use the
actual returned children and the same raw guard. Constructor readback
includes coherent cache hits. No returned profile is a premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredProfile
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
variable {Symbol Guard : Type} {rowLimit arityLimit : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual ordinary head reconstruction retains the exact original profile limits. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (available : Available before value)
    (profile : NodeShape rowLimit arityLimit value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ NodeShape rowLimit arityLimit result := by
  have initialDomain := NodeShape.domain value profile
  have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.head actual semantic available initialDomain
  refine ⟨physical.1, physical.2.1, physical.2.2.1, ?_⟩
  cases actual with
  | read fuel exposed middle read built =>
      cases initialDomain with
      | empty =>
          have same := MergedSourceExposure.Result.done.inj (by
            simpa only [MergedFreshOrdinaryExposure.nodeEdges] using read)
          rcases same with ⟨rfl, rfl⟩
          have reduced : run (makeNode ([] : List (EdgeValue Symbol Guard))) before = (.empty, before) := by
            simp [makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]
          rw [reduced] at built
          rcases Prod.mk.inj built with ⟨rfl, rfl⟩
          trivial
      | @ordinary edges entry depth free _ =>
          have same := MergedSourceExposure.Result.done.inj (by
            simpa only [MergedFreshOrdinaryExposure.nodeEdges] using read)
          rcases same with ⟨rfl, rfl⟩
          have facts := semantic.ready.semantic.1.normal.facts
          have resident := resident_edges before facts.linked _ available.resident
          have result := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode edges before facts.coherent
            facts.linked resident profile.2 profile.1
          simpa only [built] using result

private def NodeResult (rows arity : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (_after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → NodeShape rows arity value → NodeShape rows arity result

private def ChildrenResult (rows arity : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (_after : State Symbol Guard) : Prop :=
  SemanticReady before → Values before values → ChildrenShape rows arity values → ChildrenShape rows arity results

private def RowsResult (rows arity : Nat) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (EdgeValue Symbol Guard)) (_after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → RowsShape rows arity edges →
    RowsShape rows arity results ∧ results.length ≤ edges.length

private theorem all_profiles (rows arity : Nat) :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode needed value before result after → NodeResult rows arity value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      RequireChildren entries index values before results after → ChildrenResult rows arity values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows entries edges before results after → RowsResult rows arity edges before results after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {before}, NodeResult rows arity value before value before := by
    intro value before _ _ profile
    exact profile
  have emptyCase : ∀ {entries : List (Int × Needed)} {before}, entries ≠ [] →
      NodeResult rows arity (.empty : Value Symbol Guard) before .empty before := by
    intro entries before _
    exact identityCase
  have ordinaryCase : ∀ {entries edges before rebuilt middle value after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (value, after) → RowsResult rows arity edges before rebuilt middle →
      NodeResult rows arity (.node entry edges depth free) before value after := by
    intro entries edges before rebuilt middle value after entry depth free _ actual built ih semantic available profile
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := resident_edges before facts.linked _ available.resident
    have current := SourceCurrentAllocatedFiniteOrdinaryRequired.rows actual semantic resident (RowsShape.domain edges profile.2)
    have output := ih semantic resident profile.2
    have middleFacts := current.2.1.ready.semantic.1.normal.facts
    have constructor := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode rebuilt middle
      middleFacts.coherent middleFacts.linked current.2.2.1 output.1 (Nat.le_trans output.2 profile.1)
    simpa only [built] using constructor
  have recursiveCase : ∀ {entries original before exposed middle value after}, entries ≠ [] →
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle value after →
      NodeResult rows arity exposed middle value after → NodeResult rows arity original before value after := by
    intro entries original before exposed middle value after _ recursive _ _ _ _ _ profile
    have domain := NodeShape.domain original profile
    cases domain <;> cases recursive
  have nilChildren : ∀ {before}, ChildrenResult rows arity ([] : List (Value Symbol Guard)) before [] before := by
    intro before _ _ _
    trivial
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenResult rows arity values before results after →
      ChildrenResult rows arity (value :: values) before (value :: results) after := by
    intro entries values before results after value index _ _ ih semantic available profile
    exact ⟨profile.1, ih semantic (fun child member => available child (List.mem_cons_of_mem _ member)) profile.2⟩
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeResult rows arity value before result middle → ChildrenResult rows arity values middle results after →
      ChildrenResult rows arity (value :: values) before (result :: results) after := by
    intro entries needed value before result middle values results after index _ actual _ firstIH restIH semantic available profile
    have first := SourceCurrentAllocatedFiniteOrdinaryRequired.node actual semantic (available _ List.mem_cons_self)
      (NodeShape.domain value profile.1)
    exact ⟨firstIH semantic (available _ List.mem_cons_self) profile.1,
      restIH first.2.1 (fun child member => first.1.available child (available child (List.mem_cons_of_mem _ member))) profile.2⟩
  have nilRows : ∀ {before}, RowsResult rows arity ([] : List (EdgeValue Symbol Guard)) before [] before := by
    intro before _ _ _
    exact ⟨True.intro, Nat.le_refl _⟩
  have rejectedCase : ∀ {entries edges before results after edge}, fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after → RowsResult rows arity edges before results after →
      RowsResult rows arity (edge :: edges) before results after := by
    intro entries edges before results after edge _ _ ih semantic resident profile
    have output := ih semantic (fun original member => resident original (List.mem_cons_of_mem _ member)) profile.2
    exact ⟨output.1, Nat.le_trans output.2 (by simp)⟩
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenResult rows arity edge.children before values middle → RowsResult rows arity edges afterEdge results after →
      RowsResult rows arity (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge _ actual built _ firstIH restIH semantic resident profile
    have initialFacts := semantic.ready.semantic.1.normal.facts
    have available := initialFacts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have childShape := EdgeShape.children edge profile.1
    have first := SourceCurrentAllocatedFiniteOrdinaryRequired.children actual semantic available
      (ChildrenShape.domain edge.children childShape)
    have output := firstIH semantic available childShape
    have facts := first.2.1.ready.semantic.1.normal.facts
    have shaped := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge edge.entry.key.symbol edge.entry.key.constraint
      values middle facts.coherent facts.cached first.2.2.1 output
      (by rw [actual.length]; exact EdgeShape.arity edge profile.1)
    have resultShape : EdgeShape rows arity result := by simpa only [built] using shaped
    have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle
      first.2.1.ready first.2.2.1
    have edgeKept : Keeps middle afterEdge := by simpa only [built] using constructor.1
    have edgeSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint
        values middle first.2.1 first.2.2.1
    have tail := restIH edgeSemantic
      (fun original member => edge_grows before afterEdge (first.1.trans edgeKept).growth original
        (resident original (List.mem_cons_of_mem _ member))) profile.2
    exact ⟨⟨resultShape, tail.1⟩, by simpa only [List.length_cons] using Nat.succ_le_succ tail.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec
      (motive_1 := fun _ value before result after _ => NodeResult rows arity value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult rows arity values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult rows arity edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec
      (motive_1 := fun _ value before result after _ => NodeResult rows arity value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult rows arity values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult rows arity edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries edges before results after actual
    exact RequireRows.rec
      (motive_1 := fun _ value before result after _ => NodeResult rows arity value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult rows arity values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult rows arity edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- A completed node graph retains its exact original uniform limits and physical return. -/
theorem node {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (available : Available before value) (profile : NodeShape rowLimit arityLimit value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ NodeShape rowLimit arityLimit result := by
  have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.node actual semantic available (NodeShape.domain value profile)
  exact ⟨physical.1, physical.2.1, physical.2.2.1, all_profiles rowLimit arityLimit |>.1 _ _ _ _ _ actual semantic available profile⟩

/-- Completed child graphs preserve the original order, arity, and every uniform descendant bound. -/
theorem children {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireChildren entries index values before results after)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rowLimit arityLimit values) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ChildrenShape rowLimit arityLimit results ∧ results.length = values.length := by
  have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.children actual semantic available (ChildrenShape.domain values profile)
  exact ⟨physical.1, physical.2.1, physical.2.2.1,
    all_profiles rowLimit arityLimit |>.2.1 _ _ _ _ _ _ actual semantic available profile, actual.length⟩

/-- Completed row graphs preserve all original limits and cannot increase their row count. -/
theorem rows {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (profile : RowsShape rowLimit arityLimit edges) :
    Keeps before after ∧ SemanticReady after ∧ Edges after results ∧ RowsShape rowLimit arityLimit results ∧ results.length ≤ edges.length := by
  have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.rows actual semantic resident (RowsShape.domain edges profile)
  exact ⟨physical.1, physical.2.1, physical.2.2.1,
    all_profiles rowLimit arityLimit |>.2.2 _ _ _ _ _ actual semantic resident profile⟩

/-- A literal successful requireAll return preserves the exact original limits. -/
theorem requireAll_done (fuel readFuel : Nat) (paths : List (List Int))
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rowLimit arityLimit values) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ChildrenShape rowLimit arityLimit results ∧ results.length = values.length := by
  have actual := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr ⟨fuel, readFuel, done⟩
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at actual
      exact children actual semantic available profile

/-- Initial resident profiles derive finite stable requireAll execution and the same output limits. -/
theorem finite (paths : List (List Int)) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rowLimit arityLimit values) :
    ∃ results after, Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ChildrenShape rowLimit arityLimit results ∧
      results.length = values.length ∧ SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) results after := by
  have closed : MergedColdReaderClosedInputs.ClosedValues values := fun value member =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before semantic.ready.semantic.1.normal.facts.coherent value
      (available value member) (NodeShape.domain value (ChildrenShape.member values profile value member))
  obtain ⟨results, after, _keeps, _available, _closed, stable⟩ :=
    SourceEqualityRequiredExecution.requireAll_complete paths values before semantic.ready available closed
  obtain ⟨fuel, readFuel, done⟩ := stable
  have verified := requireAll_done fuel readFuel paths values results before after
    (done fuel readFuel (Nat.le_refl _) (Nat.le_refl _)) semantic available profile
  exact ⟨results, after, verified.1, verified.2.1, verified.2.2.1, verified.2.2.2.1, verified.2.2.2.2, fuel, readFuel, done⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredProfile
