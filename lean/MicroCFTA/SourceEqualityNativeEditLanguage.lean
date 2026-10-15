import MicroCFTA.SourceEqualityNativeEditEffects
import MicroCFTA.SourceEqualityEditMeaning
import MicroCFTA.SourceEqualityRequiredHeadLanguage

/-!
# Exact independent language of scoped simultaneous native edits

Actual native leaves derive their target intersection laws at their real
cache states. Constructor and head receipts derive all remaining premises.
The proof supplies no global callback or whole-worker language law.
-/
namespace MicroCFTA.SourceEqualityNativeEditLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityEdits SourceEqualityNativeEditGraph SourceEqualityEditMeaning
open SourceEqualityNativeEditEffects SourceEqualityNativeScoped
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

private theorem node_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)
    {edits value before result after} (trace : EditNode (width := width) emptyGuard conjoin edits value before result after)
    (captured : Captured base edits) (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap value) (closed : value.free = []) :
    Keeps before.machine.heap after.machine.heap ∧ IdleReady emptyGuard conjoin after ∧ Available after.machine.heap result ∧ result.free = [] := by
  have checked := SourceEqualityNativeEditEffects.node emptyGuard conjoin base trace captured retained ready available closed
  exact ⟨checked.2.1, checked.1, checked.2.2⟩

private theorem children_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)
    {entries index values before results after} (trace : EditChildren (width := width) emptyGuard conjoin entries index values before results after)
    (captured : Captured base (.editBelow entries)) (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    Keeps before.machine.heap after.machine.heap ∧ IdleReady emptyGuard conjoin after ∧ Values after.machine.heap results ∧ ClosedValues results := by
  have checked := SourceEqualityNativeEditEffects.children emptyGuard conjoin base trace captured retained ready available closed
  exact ⟨checked.2.1, checked.1, checked.2.2⟩

private theorem rows_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)
    {entries edges before results after} (trace : EditRows (width := width) emptyGuard conjoin entries edges before results after)
    (captured : Captured base (.editBelow entries)) (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Edges before.machine.heap edges) (closed : ClosedEdges edges) :
    Keeps before.machine.heap after.machine.heap ∧ IdleReady emptyGuard conjoin after ∧ Edges after.machine.heap results ∧ ClosedEdges results := by
  have checked := SourceEqualityNativeEditEffects.rows emptyGuard conjoin base trace captured retained ready available closed
  exact ⟨checked.2.1, checked.1, checked.2.2⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)
variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
variable (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
local notation "condition" => meaning holds ambient

private def NodeExact (edits : Edits (Value Symbol Guard)) (value : Value Symbol Guard)
    (before : NativeState width Symbol Guard) (result : Value Symbol Guard) : Prop :=
  SourceEqualityEdits.Valid edits → Captured base edits →
    Keeps base before.machine.heap → IdleReady emptyGuard conjoin before → Available before.machine.heap value → value.free = [] →
      ∀ term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches condition edits term

private def ChildrenExact (entries : List (Int × Edits (Value Symbol Guard))) (index : Nat) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (results : List (Value Symbol Guard)) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → Captured base (.editBelow entries) →
    Keeps base before.machine.heap → IdleReady emptyGuard conjoin before → Values before.machine.heap values → ClosedValues values →
      ∀ terms, All₂ (meaning holds ambient) results terms ↔
        All₂ (meaning holds ambient) values terms ∧ Forest condition entries index terms

private def RowsExact (entries : List (Int × Edits (Value Symbol Guard))) (edges : List (EdgeValue Symbol Guard))
    (before : NativeState width Symbol Guard) (results : List (EdgeValue Symbol Guard)) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → Captured base (.editBelow entries) →
    Keeps base before.machine.heap → IdleReady emptyGuard conjoin before → Edges before.machine.heap edges → ClosedEdges edges →
      ∀ term, (∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) ↔
        ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches condition (.editBelow entries) term

local notation "NodeLaw" => NodeExact (width := width) emptyGuard conjoin base holds ambient
local notation "ChildrenLaw" => ChildrenExact (width := width) emptyGuard conjoin base holds ambient
local notation "RowsLaw" => RowsExact (width := width) emptyGuard conjoin base holds ambient

include conjoined in
private theorem all_exact :
    (∀ edits (value : Value Symbol Guard) before result after,
      EditNode emptyGuard conjoin edits value before result after → NodeLaw edits value before result) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      EditChildren emptyGuard conjoin entries index values before results after → ChildrenLaw entries index values before results) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      EditRows emptyGuard conjoin entries edges before results after → RowsLaw entries edges before results) := by
  have leafCase : ∀ {action value before result after},
      Step emptyGuard conjoin action value before result after → NodeLaw (.editAt action) value before result := by
    intro action value before result after actual _ laws retained semantic available closed term
    have captured : Available base action ∧ action.free = [] := by simpa only [Captured, All] using laws
    have checked := actual.verified semantic (retained.available action captured.1) available captured.2 closed holds conjoined
    simpa only [Matches] using checked.2.2.2.2 ambient term
  have emptyCase : ∀ {entries : List (Int × Edits (Value Symbol Guard))} {state},
      NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty := by
    intro entries state _ _ _ _ _ _ term
    simp only [meaning, false_and]
  have ordinaryCase : ∀ {entries edges before rebuilt middle result heap entry depth free},
      EditRows emptyGuard conjoin entries edges before rebuilt middle → run (makeNode rebuilt) middle.machine.heap = (result, heap) →
      RowsLaw entries edges before rebuilt → NodeLaw (.editBelow entries) (.node entry edges depth free) before result := by
    intro entries edges before rebuilt middle result heap entry depth free trace rebuiltEq rowsIH valid laws retained semantic available closed term
    have facts := semantic.semantic.ready.semantic.1.normal.facts
    have resident : Edges before.machine.heap edges := InternedEdgeResidency.resident_edges before.machine.heap facts.linked _ available.resident
    have closedEdges := MergedColdReaderClosed.node_children_closed before.machine.heap facts entry edges depth free available closed
    have checked := rows_verified emptyGuard conjoin base trace laws retained semantic resident closedEdges
    have middleSemantic := checked.2.1
    have actual := MergedColdInterpretation.makeNode_exact middle.machine.heap middleSemantic.semantic.ready.semantic.1.normal.facts
      (meaning holds ambient) rebuilt checked.2.2.1 holds (InternedGuardedLanguage.laws holds ambient) term
    have readback : meaning holds ambient result term ↔
        ∃ edge ∈ rebuilt, EdgeMeaning (meaning holds ambient) holds edge term := by simpa only [rebuiltEq] using actual
    rw [readback, rowsIH valid laws retained semantic resident closedEdges term,
      (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term]
    constructor
    · rintro ⟨edge, member, accepted, matched⟩
      exact ⟨⟨edge, member, accepted⟩, matched⟩
    · rintro ⟨⟨edge, member, accepted⟩, matched⟩
      exact ⟨edge, member, accepted, matched⟩
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.machine.heap exposed heap →
      EditNode emptyGuard conjoin (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) result → NodeLaw (.editBelow entries) original before result := by
    intro entries original before exposed heap result after _ trace _ bodyIH valid laws retained semantic available closed term
    have nextSemantic := SourceEqualityRequiredSemanticCache.head trace semantic.semantic available closed
    have checked := trace.verified semantic.semantic.ready available closed
    rw [bodyIH valid laws (retained.trans checked.1) (semantic.advance heap checked.1 nextSemantic) checked.2.1 checked.2.2.1 term,
      SourceEqualityRequiredHeadLanguage.head_exact trace semantic.semantic available closed holds ambient term]
  have nilChildren : ∀ {entries index state}, ChildrenLaw entries index ([] : List (Value Symbol Guard)) state [] := by
    intro entries index state _ _ _ _ _ _ terms
    cases terms with
    | nil => exact ⟨fun accepted => ⟨accepted, trivial⟩, fun accepted => accepted.1⟩
    | cons term terms =>
        constructor
        · intro impossible; cases impossible
        · rintro ⟨impossible, _⟩; cases impossible
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      EditChildren emptyGuard conjoin entries (index + 1) values before results after → ChildrenLaw entries (index + 1) values before results →
      ChildrenLaw entries index (value :: values) before (value :: results) := by
    intro entries values before results after value index absent _ restIH valid laws retained semantic available closed terms
    have tailExact := restIH valid laws retained semantic
      (fun child member => available child (List.mem_cons_of_mem _ member))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    cases terms with
    | nil =>
        constructor
        · intro impossible; cases impossible
        · rintro ⟨impossible, _⟩; cases impossible
    | cons term terms =>
        constructor
        · intro accepted
          cases accepted with
          | cons first rest =>
              obtain ⟨original, required⟩ := (tailExact terms).mp rest
              refine ⟨.cons first original, ?_, required⟩
              intro edits found
              rw [absent] at found
              cases found
        · rintro ⟨original, required⟩
          cases original with
          | cons first rest => exact .cons first ((tailExact terms).mpr ⟨rest, required.2⟩)
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits →
      EditNode emptyGuard conjoin edits value before result middle → EditChildren emptyGuard conjoin entries (index + 1) values middle results after →
      NodeLaw edits value before result → ChildrenLaw entries (index + 1) values middle results →
      ChildrenLaw entries index (value :: values) before (result :: results) := by
    intro entries edits value before result middle values results after index found first _ firstIH restIH valid laws retained semantic available closed terms
    have member := SourceEqualityNeededMap.lookup_mem _ entries edits found
    have childValid : SourceEqualityEdits.Valid edits := by
      rw [SourceEqualityEdits.Valid] at valid
      exact valid.2 _ _ member
    have childLaws : Captured base edits := by
      have originalLaws := laws
      rw [Captured, All] at originalLaws
      exact originalLaws _ _ member
    have firstAvailable := available value List.mem_cons_self
    have firstClosed := closed value List.mem_cons_self
    have checked := node_verified emptyGuard conjoin base first childLaws retained semantic firstAvailable firstClosed
    have tailExact := restIH valid laws (retained.trans checked.1) checked.2.1
      (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    have firstExact := firstIH childValid childLaws retained semantic firstAvailable firstClosed
    cases terms with
    | nil =>
        constructor
        · intro impossible; cases impossible
        · rintro ⟨impossible, _⟩; cases impossible
    | cons term terms =>
        constructor
        · intro accepted
          cases accepted with
          | cons initial rest =>
              obtain ⟨originalFirst, matched⟩ := (firstExact term).mp initial
              obtain ⟨originalRest, required⟩ := (tailExact terms).mp rest
              refine ⟨.cons originalFirst originalRest, ?_, required⟩
              intro child selected
              have same := Option.some.inj (found.symm.trans selected)
              exact same ▸ matched
        · rintro ⟨original, required⟩
          cases original with
          | cons initial rest =>
              exact .cons ((firstExact term).mpr ⟨initial, required.1 edits found⟩)
                ((tailExact terms).mpr ⟨rest, required.2⟩)
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state [] := by
    intro entries state _ _ _ _ _ _ term
    simp
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin entries edges (advanceHeap middle heap) results after → ChildrenLaw entries 0 edge.children before values →
      RowsLaw entries edges (advanceHeap middle heap) results → RowsLaw entries (edge :: edges) before (result :: results) := by
    intro entries before values middle result heap edges results after edge childTrace rebuilt _ childIH restIH valid laws retained semantic resident closed term
    have facts := semantic.semantic.ready.semantic.1.normal.facts
    have available : Values before.machine.heap edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have checked := children_verified emptyGuard conjoin base childTrace laws retained semantic available (closed edge List.mem_cons_self)
    have middleSemantic := checked.2.1
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.machine.heap middleSemantic.semantic checked.2.2.1
    have edgeChecked := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.machine.heap middleSemantic.semantic.ready checked.2.2.1
    have heapSemantic : SemanticReady heap := by simpa only [rebuilt] using edgeSemantic
    have edgeKeeps : Keeps middle.machine.heap heap := by simpa only [rebuilt] using edgeChecked.1
    have firstKeeps := checked.1.trans edgeKeeps
    have tailExact := restIH valid laws (retained.trans firstKeeps) (middleSemantic.advance heap edgeKeeps heapSemantic)
      (fun original member => InternedEdgeResidency.edge_grows before.machine.heap heap firstKeeps.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) term
    have childExact := childIH valid laws retained semantic available (closed edge List.mem_cons_self)
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.machine.heap middleSemantic.semantic.ready.semantic.1.normal.facts
      edge.entry.key.symbol edge.entry.key.constraint values checked.2.2.1
    have actualFields : result.entry.key.symbol = edge.entry.key.symbol ∧
        result.entry.key.constraint = edge.entry.key.constraint ∧ result.children = values := by simpa only [rebuilt] using fields
    have ordered := (show SourceEqualityNeededMap.Ascending entries ∧ _ from
      (by simpa only [SourceEqualityEdits.Valid] using valid)).1
    have firstExact : EdgeMeaning (meaning holds ambient) holds result term ↔
        EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches condition (.editBelow entries) term := by
      unfold EdgeMeaning
      rw [actualFields.1, actualFields.2.1, actualFields.2.2]
      constructor
      · rintro ⟨terms, shape, runs, guard⟩
        obtain ⟨original, required⟩ := (childExact terms).mp runs
        have matched := (forest_zero condition entries ordered edge.entry.key.symbol terms).mp required
        exact ⟨⟨terms, shape, original, guard⟩, by simpa only [shape] using matched⟩
      · rintro ⟨⟨terms, shape, runs, guard⟩, matched⟩
        have required := (forest_zero condition entries ordered edge.entry.key.symbol terms).mpr (by simpa only [shape] using matched)
        exact ⟨terms, shape, (childExact terms).mpr ⟨runs, required⟩, guard⟩
    constructor
    · rintro ⟨output, member, accepted⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨edge, List.mem_cons_self, firstExact.mp accepted⟩
      · obtain ⟨original, member, accepted⟩ := tailExact.mp ⟨output, member, accepted⟩
        exact ⟨original, List.mem_cons_of_mem _ member, accepted⟩
    · rintro ⟨original, member, accepted⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨result, List.mem_cons_self, firstExact.mpr accepted⟩
      · obtain ⟨output, member, accepted⟩ := tailExact.mpr ⟨original, member, accepted⟩
        exact ⟨output, List.mem_cons_of_mem _ member, accepted⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec
      (motive_1 := fun edits value before result _ _ => NodeLaw edits value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenLaw entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsLaw entries edges before results)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) consCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec
      (motive_1 := fun edits value before result _ _ => NodeLaw edits value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenLaw entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsLaw entries edges before results)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec
      (motive_1 := fun edits value before result _ _ => NodeLaw edits value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenLaw entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsLaw entries edges before results)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) consCase trace

include conjoined

/-- Actual node edits accept exactly the original terms that satisfy the retained leaf conditions. -/
theorem node_exact {edits : Edits (Value Symbol Guard)} {value result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (trace : EditNode emptyGuard conjoin edits value before result after) (valid : SourceEqualityEdits.Valid edits)
    (laws : Captured base edits)
    (retained : Keeps base before.machine.heap) (semantic : IdleReady emptyGuard conjoin before) (available : Available before.machine.heap value) (closed : value.free = []) :
    ∀ term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches condition edits term :=
  (all_exact emptyGuard conjoin base holds ambient conjoined).1 edits value before result after trace valid laws retained semantic available closed

/-- Actual child scans retain their original ordered forest and exactly the selected conditions. -/
theorem children_exact {entries index values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin entries index values before results after) (valid : SourceEqualityEdits.Valid (.editBelow entries))
    (laws : Captured base (.editBelow entries))
    (retained : Keeps base before.machine.heap) (semantic : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∀ terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ Forest condition entries index terms :=
  (all_exact emptyGuard conjoin base holds ambient conjoined).2.1 entries index values before results after trace valid laws retained semantic available closed

/-- Actual row scans retain their full original alternative language with the below-node condition. -/
theorem rows_exact {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin entries edges before results after) (valid : SourceEqualityEdits.Valid (.editBelow entries))
    (laws : Captured base (.editBelow entries))
    (retained : Keeps base before.machine.heap) (semantic : IdleReady emptyGuard conjoin before) (resident : Edges before.machine.heap edges) (closed : ClosedEdges edges) :
    ∀ term, (∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) ↔
      ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches condition (.editBelow entries) term :=
  (all_exact emptyGuard conjoin base holds ambient conjoined).2.2 entries edges before results after trace valid laws retained semantic resident closed

end MicroCFTA.SourceEqualityNativeEditLanguage
