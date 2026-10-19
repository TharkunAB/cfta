import MicroCFTA.SourceCurrentStoredReconstructionPath
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Publication histories through actual required and projection calls

Each actual stored unfolding derives its source publication history.
The ordered readers compose these histories at their exact return heaps.
Ordinary constructor effects add no Mu record. Successful graph calls
retain their literal histories without a language or future-call premise.
-/
namespace MicroCFTA.SourceCurrentRequiredPublicationHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (leaves input encode Replacements inputs_available)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityRequiredGraph
open SourceCurrentNativeMuPublication (History)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual unfolding has its own publication history, including pending outcomes. -/
theorem unfold (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (available : Available before value) :
    Nonempty (History before (InternedFreshOrdinaryStoredSubstitution.unfold value before).state) := by
  cases value with
  | empty | reference | node | union => exact ⟨.refl before⟩
  | mu entry body depth ordinary =>
    let environment := fun name => if name = InternedBinderProtocol.Reference.interned entry.identity
      then some (Value.mu entry body depth ordinary) else none
    have bodyAvailable : Available before body := available.children body (by simp [children])
    have replacements : Replacements before environment := by
      intro name value found
      dsimp only [environment] at found
      split at found
      · cases found; exact available
      · cases found
    have context : SourceCurrentConstrainedCapSourceHistory.Context before ((leaves body).map (input environment)) :=
      ⟨⟨ready.semantic.1.normal,inputs_available body environment before bodyAvailable replacements,
        ready.semantic.1.profiles,ready.semantic.1.freeNames⟩,ready.semantic.2⟩
    exact SourceCurrentNativeMuPublication.build_history (encode (leaves body) [] body) _ before context

private theorem collect (fuel : Nat) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (available : Values before pending) :
    Nonempty (History before (MergedFreshOrdinaryExposure.collect fuel before seen pending).state) := by
  induction fuel generalizing before seen pending with
  | zero => cases pending <;> exact ⟨.refl before⟩
  | succ fuel ih =>
    cases pending with
    | nil => exact ⟨.refl before⟩
    | cons value rest =>
      have own := available value List.mem_cons_self
      have tail : Values before rest := fun value member => available value (List.mem_cons_of_mem _ member)
      cases value with
      | empty => exact ih before semantic costs seen rest tail
      | reference => exact ⟨.refl before⟩
      | node entry edges depth free =>
        simpa only [MergedFreshOrdinaryExposure.collect,SourceEqualityAnnotationExposure.prepend_state] using
          ih before semantic costs seen rest tail
      | union entry members depth free =>
        by_cases visited : entry.identity ∈ seen
        · simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using ih before semantic costs seen rest tail
        · have next : Values before (members ++ rest) := by
            intro value member
            rcases List.mem_append.mp member with first | later
            · exact own.children value first
            · exact tail value later
          simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited] using
            ih before semantic costs (entry.identity :: seen) (members ++ rest) next
      | mu entry body depth ordinary =>
        by_cases visited : entry.identity ∈ seen
        · simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using ih before semantic costs seen rest tail
        · obtain ⟨value,after,done,kept,afterSemantic,valueAvailable,_⟩ :=
            SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) before semantic own
          obtain ⟨first⟩ := unfold (.mu entry body depth ordinary) before semantic.ready own
          have actualFirst : History before after := by simpa only [done,Outcome.state] using first
          have afterCosts : CostHeap after := by
            simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
              (.mu entry body depth ordinary) before semantic.ready.semantic.1 semantic.ready.semantic.2 costs own
          have next : Values after (value :: rest) := by
            intro value member
            rcases List.mem_cons.mp member with rfl | later
            · exact valueAvailable
            · exact kept.available value (tail value later)
          obtain ⟨last⟩ := ih after afterSemantic afterCosts (entry.identity :: seen) (value :: rest) next
          exact ⟨by simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited,done] using History.trans actualFirst last⟩

private theorem nodeEdges (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Nonempty (History before (MergedFreshOrdinaryExposure.nodeEdges fuel value before).state) := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current) (currentCosts : CostHeap current)
      (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Nonempty (History current (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical.state) := by
    rw [SourceEqualityAnnotationExposure.canonical_state]
    exact collect fuel current currentSemantic currentCosts [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact ⟨.refl before⟩
  | union => exact fallback before semantic costs _ available
  | mu entry body depth ordinary =>
    obtain ⟨result,after,done,kept,afterSemantic,_resultAvailable,_⟩ :=
      SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) before semantic available
    obtain ⟨first⟩ := unfold (.mu entry body depth ordinary) before semantic.ready available
    have actualFirst : History before after := by simpa only [done,Outcome.state] using first
    have afterCosts : CostHeap after := by
      simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
        (.mu entry body depth ordinary) before semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
    obtain ⟨last⟩ := fallback after afterSemantic afterCosts (.mu entry body depth ordinary) (kept.available _ available)
    cases result with
    | node => exact ⟨by simpa only [MergedFreshOrdinaryExposure.nodeEdges,done,MergedSourceExposure.Result.state] using actualFirst⟩
    | empty | reference | union | mu =>
      exact ⟨by simpa only [MergedFreshOrdinaryExposure.nodeEdges,done] using History.trans actualFirst last⟩

/-- A successful actual row read extends the physical publication history. -/
theorem read {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : Read value before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Nonempty (History before after) := by
  cases actual with
  | done fuel completed =>
    simpa only [completed,MergedSourceExposure.Result.state] using nodeEdges fuel value before semantic costs available

/-- An actual Head composes row exposure with its literal no-new-Mu node constructor. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Nonempty (History before after) := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
    obtain ⟨first⟩ := read (.done fuel exposed) semantic costs available
    have last : History middle after := by
      have old := InternedShallowHeap.makeNode_noNewMu edges middle
      rw [rebuilt] at old
      exact .retain middle after old
    exact ⟨.trans first last⟩

/-- Ordered actual reads compose histories at each exact returned heap. -/
theorem readAll {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) : Nonempty (History before after) := by
  induction actual with
  | nil => exact ⟨.refl _⟩
  | cons first rest ih =>
    obtain ⟨initial⟩ := read first semantic costs (available _ List.mem_cons_self)
    have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
    obtain ⟨later⟩ := ih effects.2.1 effects.2.2.1
      (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
    exact ⟨.trans initial later⟩

/-- An actual source union retains its ordered reads and literal final node constructor. -/
theorem union {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) : Nonempty (History before after) := by
  cases actual with
  | @node edges middle result after reads built =>
    obtain ⟨first⟩ := readAll reads semantic costs available
    have old := InternedShallowHeap.makeNode_noNewMu edges middle
    rw [built] at old
    exact ⟨.trans first (.retain _ _ old)⟩

private def NodeLaw (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Nonempty (History before after)

private def ValuesLaw (values : List (Value Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Values before values → Nonempty (History before after)

private def EdgesLaw (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges → Nonempty (History before after)

private theorem projection :
    (∀ path (value : Value Symbol Guard) before result after,
      Project path value before result after → NodeLaw value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before values after,
      ProjectRows path index edges before values after → EdgesLaw edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeLaw value state state := by
    intro value state _ _ _; exact ⟨.refl _⟩
  have emptyCase : ∀ {state}, NodeLaw (.empty : Value Symbol Guard) state state := by
    intro state _ _ _; exact ⟨.refl _⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → EdgesLaw edges before middle →
      NodeLaw (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free rows joined ih semantic costs available
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨first⟩ := ih semantic costs resident
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    obtain ⟨last⟩ := union joined effects.2.1 effects.2.2.1 effects.2.2.2
    exact ⟨.trans first last⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeLaw exposed middle after → NodeLaw original before after := by
    intro original before exposed middle path index result after _ actual _ ih semantic costs available
    obtain ⟨first⟩ := head actual semantic costs available
    have effects := SourceEqualityProjectionCosts.head_effects actual semantic costs available
    obtain ⟨last⟩ := ih effects.2.1 effects.2.2.1 effects.2.2.2
    exact ⟨.trans first last⟩
  have nilCase : ∀ {state}, EdgesLaw ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _; exact ⟨.refl _⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      EdgesLaw edges before after → EdgesLaw (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic costs resident
    exact ih semantic costs (fun edge member => resident edge (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeLaw child before middle →
      EdgesLaw edges middle after → EdgesLaw (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found called _ firstIH restIH semantic costs resident
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    obtain ⟨first⟩ := firstIH semantic costs available
    have effects := SourceEqualityProjectionCosts.project_effects called semantic costs available
    obtain ⟨last⟩ := restIH effects.2.1 effects.2.2.1
      (fun edge member => InternedEdgeResidency.edge_grows before middle effects.1.growth edge
        (resident edge (List.mem_cons_of_mem _ member)))
    exact ⟨.trans first last⟩
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ edges before _ after _ => EdgesLaw edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before values after actual
    exact ProjectRows.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ edges before _ after _ => EdgesLaw edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- An actual path projection composes its selected children, Head calls, and source unions. -/
theorem project {path value before result after}
    (actual : Project (Symbol := Symbol) (Guard := Guard) path value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Nonempty (History before after) := projection.1 _ _ _ _ _ actual semantic costs available

/-- Actual row projection follows each retained selected child at its own starting heap. -/
theorem projectRows {path index edges before values after}
    (actual : ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Edges before edges) :
    Nonempty (History before after) := projection.2 _ _ _ _ _ _ actual semantic costs available

/-- Forest projection retains the actual root union or selected path history. -/
theorem forest {path values before result after}
    (actual : Forest (Symbol := Symbol) (Guard := Guard) path values before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Nonempty (History before after) := by
  cases actual with
  | root actual => exact union actual semantic costs available
  | missing => exact ⟨.refl _⟩
  | selected found actual => exact project actual semantic costs (available _ (select_member found))

private theorem required_effects {needed value before result after}
    (actual : RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result := by
  obtain ⟨kept,semantic,costs,_,available⟩ := SourceCurrentRequiredHeapEffects.node (fun _ => True)
    actual semantic costs (by intro _ _ _; trivial) available
  exact ⟨kept,semantic,costs,available⟩

private theorem children_effects {entries index values before results after}
    (actual : RequireChildren (Symbol := Symbol) (Guard := Guard) entries index values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Values after results := by
  obtain ⟨kept,semantic,costs,_,available⟩ := SourceCurrentRequiredHeapEffects.children (fun _ => True)
    actual semantic costs (by intro _ _ _; trivial) available
  exact ⟨kept,semantic,costs,available⟩

private theorem required_histories :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode needed value before result after → NodeLaw value before after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      RequireChildren entries index values before results after → ValuesLaw values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows entries edges before results after → EdgesLaw edges before after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeLaw value state state := by
    intro value state _ _ _; exact ⟨.refl _⟩
  have emptyCase : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {state},
      entries ≠ [] → NodeLaw (.empty : Value Symbol Guard) state state := by
    intro entries state _ _ _ _; exact ⟨.refl _⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (result, after) → EdgesLaw edges before middle →
      NodeLaw (.node entry edges depth free) before after := by
    intro entries edges before rebuilt middle result after entry depth free _ actual built ih semantic costs available
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨first⟩ := ih semantic costs resident
    have old := InternedShallowHeap.makeNode_noNewMu rebuilt middle
    rw [built] at old
    exact ⟨.trans first (.retain _ _ old)⟩
  have recursiveCase : ∀ {entries original before exposed middle result after},
      entries ≠ [] → Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeLaw exposed middle after → NodeLaw original before after := by
    intro entries original before exposed middle result after _ _ actual _ ih semantic costs available
    obtain ⟨first⟩ := head actual semantic costs available
    have effects := SourceEqualityProjectionCosts.head_effects actual semantic costs available
    obtain ⟨last⟩ := ih effects.2.1 effects.2.2.1 effects.2.2.2
    exact ⟨.trans first last⟩
  have nilChildren : ∀ {state}, ValuesLaw ([] : List (Value Symbol Guard)) state state := by
    intro state _ _ _; exact ⟨.refl _⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ValuesLaw values before after → ValuesLaw (value :: values) before after := by
    intro entries values before results after value index _ _ ih semantic costs available
    exact ih semantic costs (fun value member => available value (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeLaw value before middle → ValuesLaw values middle after → ValuesLaw (value :: values) before after := by
    intro entries needed value before result middle values results after index _ actual _ firstIH restIH semantic costs available
    obtain ⟨first⟩ := firstIH semantic costs (available value List.mem_cons_self)
    have effects := required_effects actual semantic costs (available value List.mem_cons_self)
    obtain ⟨last⟩ := restIH effects.2.1 effects.2.2.1
      (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
    exact ⟨.trans first last⟩
  have nilRows : ∀ {state}, EdgesLaw ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _; exact ⟨.refl _⟩
  have rejectedCase : ∀ {entries edges before results after edge},
      SourceEqualityNeeded.fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      EdgesLaw edges before after → EdgesLaw (edge :: edges) before after := by
    intro entries edges before results after edge _ _ ih semantic costs resident
    exact ih semantic costs (fun edge member => resident edge (List.mem_cons_of_mem _ member))
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      SourceEqualityNeeded.fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ValuesLaw edge.children before middle → EdgesLaw edges afterEdge after → EdgesLaw (edge :: edges) before after := by
    intro entries before values middle result afterEdge edges results after edge _ actual built _ childIH restIH semantic costs resident
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    obtain ⟨first⟩ := childIH semantic costs available
    have effects := children_effects actual semantic costs available
    have edgeFacts := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle
      effects.2.1.ready effects.2.2.2
    have edgeSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values
        middle effects.2.1 effects.2.2.2
    have edgeKeeps : Keeps middle afterEdge := by simpa only [built] using edgeFacts.1
    have edgeCosts : CostHeap afterEdge := by
      have old : InternedShallowHeap.NoNewMu middle afterEdge := by
        have same : (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2.nodeRecords = middle.nodeRecords := rfl
        rw [built] at same
        intro key entry body depth ordinary stored
        exact same ▸ stored
      exact InternedFreshOrdinaryCostHeap.preserve middle afterEdge effects.2.2.1 old
    obtain ⟨last⟩ := restIH edgeSemantic edgeCosts
      (fun edge member => InternedEdgeResidency.edge_grows before afterEdge (effects.1.trans edgeKeeps).growth edge
        (resident edge (List.mem_cons_of_mem _ member)))
    have edgeHistory : History middle afterEdge := by
      have old : InternedShallowHeap.NoNewMu middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 :=
        by intro key entry body depth ordinary stored; exact stored
      rw [built] at old
      exact .retain _ _ old
    exact ⟨.trans first (.trans edgeHistory last)⟩
  refine ⟨?_,?_,?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ values before _ after _ => ValuesLaw values before after)
      (motive_3 := fun _ edges before _ after _ => EdgesLaw edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ values before _ after _ => ValuesLaw values before after)
      (motive_3 := fun _ edges before _ after _ => EdgesLaw edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries edges before results after actual
    exact RequireRows.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ values before _ after _ => ValuesLaw values before after)
      (motive_3 := fun _ edges before _ after _ => EdgesLaw edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- An actual required-node call derives its completed publication history. -/
theorem required {needed value before result after}
    (actual : RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Nonempty (History before after) := required_histories.1 _ _ _ _ _ actual semantic costs available

/-- Actual required children compose the histories of selected calls in source order. -/
theorem children {entries index values before results after}
    (actual : RequireChildren (Symbol := Symbol) (Guard := Guard) entries index values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Nonempty (History before after) := required_histories.2.1 _ _ _ _ _ _ actual semantic costs available

/-- Actual required rows retain child histories and exact edge construction intervals. -/
theorem rows {entries edges before results after}
    (actual : RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Edges before edges) :
    Nonempty (History before after) := required_histories.2.2 _ _ _ _ _ actual semantic costs available

end MicroCFTA.SourceCurrentRequiredPublicationHistory
