import MicroCFTA.SourceCurrentRequiredSupport

/-!
# Finite requireAll execution with open unrelated siblings

The induction decreases the actual finite Needed trie. Selected child
requests use their original path-local support. The list scans preserve
unselected values. Recursive heads return ordinary rows and the derived
child domains. Actual constructors preserve semantic heaps and availability.
The result need not be closed. Its support at the old anchor is not assumed.
-/
namespace MicroCFTA.SourceCurrentRequiredComplete
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (edge_grows)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache SourceCurrentRequiredSupport

private def ChildComplete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) : Prop :=
  ∀ index needed, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed →
    ∀ (value : Value Symbol Guard) before, SemanticReady before → Available before value →
      Grows anchor before → NodeSupport unconstrained anchor needed value →
      ∃ result after, RequireNode needed value before result after ∧ Keeps before after ∧
        SemanticReady after ∧ Available after result

private def ChildrenSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (offset : Nat) (values : List (Value Symbol Guard)) : Prop :=
  ∀ query needed, SourceEqualityNeededMap.lookup (Int.ofNat (offset + query)) entries = some needed →
    ∀ value, values[query]? = some value → NodeSupport unconstrained anchor needed value

private theorem children_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (entries : List (Int × Needed)) (callbacks : ChildComplete unconstrained anchor entries)
    (offset : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ChildrenSupport unconstrained anchor entries offset values) :
    ∃ results after, RequireChildren entries offset values before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Values after results := by
  induction values generalizing offset before with
  | nil => exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic, by simp [Values]⟩
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have restAvailable : Values before values := fun child member => available child (List.mem_cons_of_mem _ member)
      have restSupport : ChildrenSupport unconstrained anchor entries (offset + 1) values := by
        intro query needed found child selected
        exact support (query + 1) needed
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) child selected
      cases found : SourceEqualityNeededMap.lookup (Int.ofNat offset) entries with
      | none =>
          obtain ⟨results, after, trace, kept, ready, resident⟩ := ih (offset + 1) before semantic
            restAvailable growth restSupport
          refine ⟨value :: results, after, .unselected offset found trace, kept, ready, ?_⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact kept.available _ firstAvailable
          · exact resident child member
      | some needed =>
          obtain ⟨result, middle, first, firstKept, middleSemantic, resultAvailable⟩ := callbacks offset needed found
            value before semantic firstAvailable growth (support 0 needed (by simpa using found) value rfl)
          obtain ⟨results, after, rest, restKept, ready, resident⟩ := ih (offset + 1) middle middleSemantic
            (fun child member => firstKept.available _ (restAvailable child member))
            (grows_trans growth firstKept.growth) restSupport
          refine ⟨result :: results, after, .selected offset found first rest, firstKept.trans restKept, ready, ?_⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact restKept.available _ resultAvailable
          · exact resident child member

private theorem rows_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (entries : List (Int × Needed)) (callbacks : ChildComplete unconstrained anchor entries)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (support : RowsSupport unconstrained anchor (.node entries) edges) :
    ∃ results after, RequireRows entries edges before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Edges after results := by
  induction edges generalizing before with
  | nil => exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic, by simp [Edges]⟩
  | cons edge edges ih =>
      have restResident : Edges before edges := fun original member => resident original (List.mem_cons_of_mem _ member)
      have restSupport : RowsSupport unconstrained anchor (.node entries) edges :=
        fun original member => support original (List.mem_cons_of_mem _ member)
      cases fit : fits (.node entries) edge.children.length with
      | false =>
          obtain ⟨results, after, trace, kept, ready, resident⟩ := ih before semantic restResident growth restSupport
          exact ⟨results, after, .rejected fit trace, kept, ready, resident⟩
      | true =>
          have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self)
          obtain ⟨values, middle, children, childKept, middleSemantic, valuesAvailable⟩ :=
            children_complete entries callbacks 0 edge.children before semantic available growth
              (by simpa only [ChildrenSupport, ForestSupport, Nat.zero_add] using support edge List.mem_cons_self)
          let actual := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle
          have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values
            middle middleSemantic.ready valuesAvailable
          have afterSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint
            values middle middleSemantic valuesAvailable
          have firstKept : Keeps before actual.2 := childKept.trans built.1
          obtain ⟨results, after, rest, restKept, ready, residentResults⟩ := ih actual.2 afterSemantic
            (fun original member => edge_grows before actual.2 firstKept.growth original (restResident original member))
            (grows_trans growth firstKept.growth) restSupport
          refine ⟨actual.1 :: results, after, .kept fit children rfl rest, firstKept.trans restKept, ready, ?_⟩
          intro original member
          rcases List.mem_cons.mp member with rfl | member
          · exact edge_grows actual.2 after restKept.growth actual.1 built.2.1
          · exact residentResults original member

private theorem ordinary_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (entries : List (Int × Needed)) (nonempty : entries ≠ [])
    (callbacks : ChildComplete unconstrained anchor entries)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (ordinary : Ordinary value)
    (support : RowsSupport unconstrained anchor (.node entries) (InternedEdgeResidency.nodeEdges value)) :
    ∃ result after, RequireNode (.node entries) value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result := by
  cases value with
  | empty => exact ⟨.empty, before, .empty nonempty, pure_keeps before semantic.ready, semantic, available⟩
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      have resident : Edges before edges := InternedEdgeResidency.resident_edges before
        semantic.ready.semantic.1.normal.facts.linked _ available.resident
      obtain ⟨rebuilt, middle, rows, kept, middleSemantic, residentRows⟩ :=
        rows_complete entries callbacks edges before semantic resident growth support
      have finished := SourceEqualityOpenOrdinaryHead.node rebuilt middle middleSemantic residentRows
      exact ⟨_, _, .ordinary nonempty rows rfl, kept.trans finished.1, finished.2.1, finished.2.2.1⟩

/-- Every supported normalized node requirement has a finite actual graph with open-input effects. -/
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (needed : Needed) (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) :
    ∃ result after, RequireNode needed value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result := by
  cases shape : needed with
  | node entries =>
      have validEntries : SourceEqualityNeededMap.Ascending entries ∧
          ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
        simpa only [shape, SourceEqualityNeeded.Valid] using valid
      have nonnegativeEntries : ∀ index child, (index, child) ∈ entries →
          0 ≤ index ∧ SourceEqualityNeededNonnegative.Nonnegative child := by
        simpa only [shape, SourceEqualityNeededNonnegative.Nonnegative] using nonnegative
      by_cases noChildren : entries = []
      · subst entries
        exact ⟨value, before, .identity, pure_keeps before semantic.ready, semantic, available⟩
      · have callbacks : ChildComplete unconstrained anchor entries := by
          intro index child found value before ready available growth supported
          have member := SourceEqualityNeededMap.lookup_mem (Int.ofNat index) entries child found
          exact node_complete unconstrained anchor anchorSemantic child (validEntries.2 _ _ member)
            (nonnegativeEntries _ _ member).2 value before ready available growth supported
        have support : NodeSupport unconstrained anchor (.node entries) value := by simpa only [shape] using support
        cases value with
        | empty => exact ⟨.empty, before, .empty noChildren, pure_keeps before semantic.ready, semantic, available⟩
        | reference name =>
            obtain ⟨path, tip⟩ := tip_exists (.node entries) (by simpa only [shape] using valid)
              (by simpa only [shape] using nonnegative)
            have nonroot : path ≠ [] := by
              intro same
              subst path
              cases tip
              exact noChildren rfl
            rcases support path tip nonroot with closed | ⟨_, trace⟩
            · simp [Value.free] at closed
            · cases trace
        | node entry edges depth free =>
            exact ordinary_complete entries noChildren callbacks (.node entry edges depth free) before
              semantic available growth True.intro (ordinary_rows support anchorSemantic semantic available)
        | union entry members depth free =>
            obtain ⟨exposed, middle, head, kept, middleSemantic, resident, ordinary, rows, _⟩ :=
              SourceCurrentRequiredSupport.head_complete support noChildren (by simpa only [shape] using valid)
                (by simpa only [shape] using nonnegative) anchorSemantic semantic available growth
            obtain ⟨result, after, body, bodyKept, afterSemantic, resultAvailable⟩ := ordinary_complete entries noChildren
              callbacks exposed middle middleSemantic resident (grows_trans growth kept.growth) ordinary rows
            exact ⟨result, after, .recursive noChildren True.intro head body, kept.trans bodyKept,
              afterSemantic, resultAvailable⟩
        | mu entry body depth ordinary =>
            obtain ⟨exposed, middle, head, kept, middleSemantic, resident, ordinary, rows, _⟩ :=
              SourceCurrentRequiredSupport.head_complete support noChildren (by simpa only [shape] using valid)
                (by simpa only [shape] using nonnegative) anchorSemantic semantic available growth
            obtain ⟨result, after, body, bodyKept, afterSemantic, resultAvailable⟩ := ordinary_complete entries noChildren
              callbacks exposed middle middleSemantic resident (grows_trans growth kept.growth) ordinary rows
            exact ⟨result, after, .recursive noChildren True.intro head body, kept.trans bodyKept,
              afterSemantic, resultAvailable⟩
termination_by sizeOf needed
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- The actual compiled forest entry completes without closing its unrelated original siblings. -/
theorem requireAll_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (paths : List (List Int)) (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (growth : Grows anchor before)
    (support : ForestSupport unconstrained anchor (build paths) values) :
    ∃ results after, Keeps before after ∧ SemanticReady after ∧ Values after results ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) results after := by
  have valid := build_valid paths
  have nonnegative := SourceEqualityNeededNonnegative.build_nonnegative paths indices
  cases compiled : build paths with
  | node entries =>
      have validEntries : SourceEqualityNeededMap.Ascending entries ∧
          ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
        simpa only [compiled, SourceEqualityNeeded.Valid] using valid
      have nonnegativeEntries : ∀ index child, (index, child) ∈ entries →
          0 ≤ index ∧ SourceEqualityNeededNonnegative.Nonnegative child := by
        simpa only [compiled, SourceEqualityNeededNonnegative.Nonnegative] using nonnegative
      have callbacks : ChildComplete unconstrained anchor entries := by
        intro index child found value before ready available growth supported
        have member := SourceEqualityNeededMap.lookup_mem (Int.ofNat index) entries child found
        exact node_complete unconstrained anchor anchorSemantic child (validEntries.2 _ _ member)
          (nonnegativeEntries _ _ member).2 value before ready available growth supported
      obtain ⟨results, after, trace, kept, afterSemantic, resident⟩ := children_complete entries callbacks 0 values before
        semantic available growth (by simpa only [compiled, ForestSupport, ChildrenSupport, Nat.zero_add] using support)
      exact ⟨results, after, kept, afterSemantic, resident, by
        simpa only [SourceEqualityRequiredExecution.requireAll, compiled] using
          SourceEqualityRequiredWorkerComplete.children_stable trace⟩

/-- An actual completed node graph has the derived effects of its supported finite execution. -/
theorem node_verified [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after)
    (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result := by
  obtain ⟨actual, final, complete, kept, ready, resident⟩ := node_complete unconstrained anchor anchorSemantic
    needed valid nonnegative value before semantic available growth support
  obtain ⟨sameValue, sameState⟩ := SourceEqualityRequiredExecution.node_unique complete trace
  cases sameValue
  cases sameState
  exact ⟨kept, ready, resident⟩

/-- Actual primary false classes derive finite requireAll execution in each retained caller heap. -/
theorem primary_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {paths : EqualityNormalize.Class} {values : List (Value Symbol Guard)} {initial anchor : State Symbol Guard}
    (gate : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths initial false anchor)
    (initialSemantic : SemanticReady initial) (initialCosts : InternedFreshOrdinaryCostHeap.Heap initial)
    (initialAvailable : Values initial values)
    (caller : State Symbol Guard) (semantic : SemanticReady caller) (available : Values caller values)
    (growth : Grows anchor caller) :
    ∃ results after, Keeps caller after ∧ SemanticReady after ∧ Values after results ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (paths.map (List.map Int.ofNat)) values caller) results after := by
  have supported := primary_domain gate initialSemantic initialCosts initialAvailable
  apply requireAll_complete unconstrained anchor supported.1 (paths.map (List.map Int.ofNat)) ?_
    values caller semantic available growth supported.2.2.2.2
  intro path member index inside
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨natural, _, rfl⟩ := List.mem_map.mp inside
  exact Int.natCast_nonneg natural

end MicroCFTA.SourceCurrentRequiredComplete
