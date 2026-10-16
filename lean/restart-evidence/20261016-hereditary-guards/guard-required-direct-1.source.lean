import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardConstructors
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequired

/-!
# Hereditary guards through actual required-path graphs

Required paths remove rows or rebuild them with their original constraints.
Each selected child retains its initial bound at the actual returned heap.
The proof verifies supplied graphs. It does not assert general completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardRequired
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
local notation "Guard" => SourceSymbolicIndex.Constraint
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
variable {Symbol Formula : Type}
variable [DecidableEq (EdgeKey Symbol (Guard Formula))]

private def NodeResult (value : Value Symbol (Guard Formula)) (before : State Symbol (Guard Formula))
    (result : Value Symbol (Guard Formula)) : Prop :=
  ∀ limit, SemanticReady before → Available before value → Node limit value → Node limit result

private def ChildrenResult (values : List (Value Symbol (Guard Formula))) (before : State Symbol (Guard Formula))
    (results : List (Value Symbol (Guard Formula))) : Prop :=
  ∀ limit, SemanticReady before → Values before values → Children limit values → Children limit results

private def RowsResult (edges : List (EdgeValue Symbol (Guard Formula))) (before : State Symbol (Guard Formula))
    (results : List (EdgeValue Symbol (Guard Formula))) : Prop :=
  ∀ limit, SemanticReady before → Edges before edges → Rows limit edges → Rows limit results

private theorem all_verified :
    (∀ needed (value : Value Symbol (Guard Formula)) before result after,
      RequireNode needed value before result after → NodeResult value before result) ∧
    (∀ entries index (values : List (Value Symbol (Guard Formula))) before results after,
      RequireChildren entries index values before results after → ChildrenResult values before results) ∧
    (∀ entries (edges : List (EdgeValue Symbol (Guard Formula))) before results after,
      RequireRows entries edges before results after → RowsResult edges before results) := by
  have identityCase : ∀ {value : Value Symbol (Guard Formula)} {before}, NodeResult value before value := by
    intro value before limit _ _ profile
    exact profile
  have emptyCase : ∀ {entries : List (Int × Needed)} {before}, entries ≠ [] →
      NodeResult (.empty : Value Symbol (Guard Formula)) before .empty := by
    intro entries before _
    exact identityCase
  have ordinaryCase : ∀ {entries edges before rebuilt middle value after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard Formula) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (value, after) → RowsResult edges before rebuilt →
      NodeResult (.node entry edges depth free) before value := by
    intro entries edges before rebuilt middle value after entry depth free _ actual built ih limit semantic available profile
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.rows actual semantic resident (Rows.domain edges profile)
    have facts := physical.2.1.ready.semantic.1.normal.facts
    have bounded := SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.makeNode rebuilt middle
      facts.coherent facts.linked physical.2.2.1 (ih limit semantic resident profile)
    simpa only [built] using bounded
  have recursiveCase : ∀ {entries original before exposed middle value after}, entries ≠ [] →
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard Formula) (.node entries) exposed middle value after →
      NodeResult exposed middle value → NodeResult original before value := by
    intro entries original before exposed middle value after _ recursive _ _ _ limit _ _ profile
    have domain := Node.domain original profile
    cases domain <;> cases recursive
  have nilChildren : ∀ {before}, ChildrenResult ([] : List (Value Symbol (Guard Formula))) before [] := by
    intro before limit _ _ _
    trivial
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard Formula) entries (index + 1) values before results after →
      ChildrenResult values before results → ChildrenResult (value :: values) before (value :: results) := by
    intro entries values before results after value index _ _ ih limit semantic available profile
    exact ⟨profile.1, ih limit semantic
      (fun child member => available child (List.mem_cons_of_mem _ member)) profile.2⟩
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard Formula) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard Formula) entries (index + 1) values middle results after →
      NodeResult value before result → ChildrenResult values middle results →
      ChildrenResult (value :: values) before (result :: results) := by
    intro entries needed value before result middle values results after index _ actual _ firstIH restIH
      limit semantic available profile
    have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.node actual semantic
      (available _ List.mem_cons_self) (Node.domain value profile.1)
    exact ⟨firstIH limit semantic (available _ List.mem_cons_self) profile.1,
      restIH limit physical.2.1
        (fun child member => physical.1.available _ (available child (List.mem_cons_of_mem _ member))) profile.2⟩
  have nilRows : ∀ {before}, RowsResult ([] : List (EdgeValue Symbol (Guard Formula))) before [] := by
    intro before limit _ _ _
    trivial
  have rejectedCase : ∀ {entries edges before results after edge}, fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard Formula) entries edges before results after → RowsResult edges before results →
      RowsResult (edge :: edges) before results := by
    intro entries edges before results after edge _ _ ih limit semantic resident profile
    exact ih limit semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member)) profile.2
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard Formula) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard Formula) entries edges afterEdge results after →
      ChildrenResult edge.children before values → RowsResult edges afterEdge results →
      RowsResult (edge :: edges) before (result :: results) := by
    intro entries before values middle result afterEdge edges results after edge _ actual built _ firstIH restIH
      limit semantic resident profile
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self)
    have childBound := Edge.children edge profile.1
    have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.children actual semantic available
      (Children.domain edge.children childBound)
    have valuesBound := firstIH limit semantic available childBound
    have facts := physical.2.1.ready.semantic.1.normal.facts
    have bounded : Edge limit result := by
      have raw := SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.makeEdge edge.entry.key.symbol
        edge.entry.key.constraint values middle facts.coherent facts.cached physical.2.2.1
        (Edge.guard edge profile.1) valuesBound
      simpa only [built] using raw
    have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle
      physical.2.1.ready physical.2.2.1
    have kept : SourceEqualityRequiredCache.Keeps middle afterEdge := by simpa only [built] using constructor.1
    have afterSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint
        values middle physical.2.1 physical.2.2.1
    have tailBound := restIH limit afterSemantic
      (fun original member => edge_grows before afterEdge (physical.1.trans kept).growth original
        (resident original (List.mem_cons_of_mem _ member))) profile.2
    exact ⟨bounded, tailBound⟩
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec
      (motive_1 := fun _ value before result _ _ => NodeResult value before result)
      (motive_2 := fun _ _ values before results _ _ => ChildrenResult values before results)
      (motive_3 := fun _ edges before results _ _ => RowsResult edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec
      (motive_1 := fun _ value before result _ _ => NodeResult value before result)
      (motive_2 := fun _ _ values before results _ _ => ChildrenResult values before results)
      (motive_3 := fun _ edges before results _ _ => RowsResult edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries edges before results after actual
    exact RequireRows.rec
      (motive_1 := fun _ value before result _ _ => NodeResult value before result)
      (motive_2 := fun _ _ values before results _ _ => ChildrenResult values before results)
      (motive_3 := fun _ edges before results _ _ => RowsResult edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- Every actual required-node return retains its complete initial guard bound. -/
theorem node {limit : Limits} {needed : Needed} {value result : Value Symbol (Guard Formula)}
    {before after : State Symbol (Guard Formula)} (actual : RequireNode needed value before result after)
    (semantic : SemanticReady before) (available : Available before value) (profile : Node limit value) : Node limit result :=
  all_verified.1 _ _ _ _ _ actual limit semantic available profile

/-- Every actual required-child return retains the same bound at each ordered position. -/
theorem children {limit : Limits} {entries : List (Int × Needed)} {index : Nat}
    {values results : List (Value Symbol (Guard Formula))} {before after : State Symbol (Guard Formula)}
    (actual : RequireChildren entries index values before results after)
    (semantic : SemanticReady before) (available : Values before values) (profile : Children limit values) : Children limit results :=
  all_verified.2.1 _ _ _ _ _ _ actual limit semantic available profile

/-- Every actual required-row return retains all nested constraints of its retained rows. -/
theorem rows {limit : Limits} {entries : List (Int × Needed)}
    {edges results : List (EdgeValue Symbol (Guard Formula))} {before after : State Symbol (Guard Formula)}
    (actual : RequireRows entries edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (profile : Rows limit edges) : Rows limit results :=
  all_verified.2.2 _ _ _ _ _ actual limit semantic resident profile

/-- A literal completed requireAll retains the original forest's hereditary guard bound. -/
theorem requireAll_done (fuel readFuel : Nat) (paths : List (List Int))
    (values results : List (Value Symbol (Guard Formula))) (before after : State Symbol (Guard Formula))
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (available : Values before values) (limit : Limits)
    (profile : Children limit values) : Children limit results := by
  have actual := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, done⟩
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at actual
      exact children actual semantic available profile

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardRequired
