import MicroCFTA.SourceEqualityEditExecution
import MicroCFTA.SourceEqualityEditMeaning
import MicroCFTA.SourceEqualityRequiredHeadLanguage

/-!
# Exact independent language of physical simultaneous edits

Only stored leaf callbacks supply completion and narrowing contracts. Mutual
graph induction derives the whole edit language from actual head exposure,
ordered child calls, and complete constructor readback.
-/
namespace MicroCFTA.SourceEqualityEditLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityEdits SourceEqualityEditGraph SourceEqualityEditMeaning
open SourceEqualityEditComplete SourceEqualityEditExecution
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

/-- One actual leaf callback completes and keeps precisely its input terms that satisfy its condition. -/
structure LeafLaw [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (condition : Action → Term Symbol → Prop) (holds : Guard → Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol) (action : Action) : Prop where
  complete : CallbackComplete call action
  language : ∀ value before result after, call action value before = .done result after →
    SemanticReady before → Available before value → value.free = [] →
    ∀ term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ condition action term

variable [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
  (condition : Action → Term Symbol → Prop) (holds : Guard → Term Symbol → Bool)
  (ambient : InternedGuardedLanguage.Env Symbol)

/-- The leaf laws supply exactly the completion premises used by verified graph effects. -/
theorem leaves_complete {edits : Edits Action} (laws : All (LeafLaw call condition holds ambient) edits) :
    All (CallbackComplete call) edits :=
  all_mono _ _ (fun _ law => law.complete) edits laws

private def NodeExact (edits : Edits Action) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) : Prop :=
  SourceEqualityEdits.Valid edits → All (LeafLaw call condition holds ambient) edits →
    SemanticReady before → Available before value → value.free = [] →
      ∀ term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches condition edits term

private def ChildrenExact (entries : List (Int × Edits Action)) (index : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → All (LeafLaw call condition holds ambient) (.editBelow entries) →
    SemanticReady before → Values before values → ClosedValues values →
      ∀ terms, All₂ (meaning holds ambient) results terms ↔
        All₂ (meaning holds ambient) values terms ∧ Forest condition entries index terms

private def RowsExact (entries : List (Int × Edits Action)) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → All (LeafLaw call condition holds ambient) (.editBelow entries) →
    SemanticReady before → Edges before edges → ClosedEdges edges →
      ∀ term, (∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) ↔
        ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches condition (.editBelow entries) term

local notation "NodeLaw" => NodeExact call condition holds ambient
local notation "ChildrenLaw" => ChildrenExact call condition holds ambient
local notation "RowsLaw" => RowsExact call condition holds ambient

private theorem all_exact :
    (∀ edits (value : Value Symbol Guard) before result after,
      EditNode call edits value before result after → NodeLaw edits value before result) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      EditChildren call entries index values before results after → ChildrenLaw entries index values before results) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      EditRows call entries edges before results after → RowsLaw entries edges before results) := by
  have leafCase : ∀ {action value before result after},
      call action value before = .done result after → NodeLaw (.editAt action) value before result := by
    intro action value before result after actual _ laws semantic available closed term
    rw [All] at laws
    simpa only [Matches] using laws.language value before result after actual semantic available closed term
  have emptyCase : ∀ {entries : List (Int × Edits Action)} {state},
      NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty := by
    intro entries state _ _ _ _ _ term
    simp only [meaning, false_and]
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      EditRows call entries edges before rebuilt middle → run (makeNode rebuilt) middle = (result, after) →
      RowsLaw entries edges before rebuilt → NodeLaw (.editBelow entries) (.node entry edges depth free) before result := by
    intro entries edges before rebuilt middle result after entry depth free trace rebuiltEq rowsIH valid laws semantic available closed term
    have facts := semantic.ready.semantic.1.normal.facts
    have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have closedEdges := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have checked := rows_verified trace (leaves_complete call condition holds ambient laws) semantic resident closedEdges
    have middleSemantic := checked.2.1
    have actual := MergedColdInterpretation.makeNode_exact middle middleSemantic.ready.semantic.1.normal.facts
      (meaning holds ambient) rebuilt checked.2.2.1 holds (InternedGuardedLanguage.laws holds ambient) term
    have readback : meaning holds ambient result term ↔
        ∃ edge ∈ rebuilt, EdgeMeaning (meaning holds ambient) holds edge term := by simpa only [rebuiltEq] using actual
    rw [readback, rowsIH valid laws semantic resident closedEdges term,
      (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term]
    constructor
    · rintro ⟨edge, member, accepted, matched⟩
      exact ⟨⟨edge, member, accepted⟩, matched⟩
    · rintro ⟨⟨edge, member, accepted⟩, matched⟩
      exact ⟨edge, member, accepted, matched⟩
  have recursiveCase : ∀ {entries original before exposed middle result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      EditNode call (.editBelow entries) exposed middle result after → NodeLaw (.editBelow entries) exposed middle result →
      NodeLaw (.editBelow entries) original before result := by
    intro entries original before exposed middle result after _ trace _ bodyIH valid laws semantic available closed term
    have nextSemantic := SourceEqualityRequiredSemanticCache.head trace semantic available closed
    have checked := trace.verified semantic.ready available closed
    rw [bodyIH valid laws nextSemantic checked.2.1 checked.2.2.1 term,
      SourceEqualityRequiredHeadLanguage.head_exact trace semantic available closed holds ambient term]
  have nilChildren : ∀ {entries index state}, ChildrenLaw entries index ([] : List (Value Symbol Guard)) state [] := by
    intro entries index state _ _ _ _ _ terms
    cases terms with
    | nil => exact ⟨fun accepted => ⟨accepted, trivial⟩, fun accepted => accepted.1⟩
    | cons term terms =>
        constructor
        · intro impossible; cases impossible
        · rintro ⟨impossible, _⟩; cases impossible
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      EditChildren call entries (index + 1) values before results after → ChildrenLaw entries (index + 1) values before results →
      ChildrenLaw entries index (value :: values) before (value :: results) := by
    intro entries values before results after value index absent _ restIH valid laws semantic available closed terms
    have tailExact := restIH valid laws semantic
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
      EditNode call edits value before result middle → EditChildren call entries (index + 1) values middle results after →
      NodeLaw edits value before result → ChildrenLaw entries (index + 1) values middle results →
      ChildrenLaw entries index (value :: values) before (result :: results) := by
    intro entries edits value before result middle values results after index found first _ firstIH restIH valid laws semantic available closed terms
    have member := SourceEqualityNeededMap.lookup_mem _ entries edits found
    have childValid : SourceEqualityEdits.Valid edits := by
      rw [SourceEqualityEdits.Valid] at valid
      exact valid.2 _ _ member
    have childLaws : All (LeafLaw call condition holds ambient) edits := by
      have originalLaws := laws
      rw [All] at originalLaws
      exact originalLaws _ _ member
    have firstAvailable := available value List.mem_cons_self
    have firstClosed := closed value List.mem_cons_self
    have checked := node_verified first (leaves_complete call condition holds ambient childLaws) semantic firstAvailable firstClosed
    have tailExact := restIH valid laws checked.2.1
      (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    have firstExact := firstIH childValid childLaws semantic firstAvailable firstClosed
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
    intro entries state _ _ _ _ _ term
    simp
  have consCase : ∀ {entries before values middle result afterEdge edges results after edge},
      EditChildren call entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      EditRows call entries edges afterEdge results after → ChildrenLaw entries 0 edge.children before values →
      RowsLaw entries edges afterEdge results → RowsLaw entries (edge :: edges) before (result :: results) := by
    intro entries before values middle result afterEdge edges results after edge childTrace rebuilt _ childIH restIH valid laws semantic resident closed term
    have facts := semantic.ready.semantic.1.normal.facts
    have available : Values before edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have checked := children_verified childTrace (leaves_complete call condition holds ambient laws) semantic available (closed edge List.mem_cons_self)
    have middleSemantic := checked.2.1
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic checked.2.2.1
    have edgeChecked := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic.ready checked.2.2.1
    have afterSemantic : SemanticReady afterEdge := by simpa only [rebuilt] using edgeSemantic
    have edgeKeeps : Keeps middle afterEdge := by simpa only [rebuilt] using edgeChecked.1
    have growth := (checked.1.trans edgeKeeps).growth
    have tailExact := restIH valid laws afterSemantic
      (fun original member => InternedEdgeResidency.edge_grows before afterEdge growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) term
    have childExact := childIH valid laws semantic available (closed edge List.mem_cons_self)
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleSemantic.ready.semantic.1.normal.facts
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

/-- Actual node edits accept exactly the original terms that satisfy the retained leaf conditions. -/
theorem node_exact {edits : Edits Action} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : EditNode call edits value before result after) (valid : SourceEqualityEdits.Valid edits)
    (laws : All (LeafLaw call condition holds ambient) edits)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    ∀ term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches condition edits term :=
  (all_exact call condition holds ambient).1 edits value before result after trace valid laws semantic available closed

/-- Actual child scans retain their original ordered forest and exactly the selected conditions. -/
theorem children_exact {entries index values before results after}
    (trace : EditChildren call entries index values before results after) (valid : SourceEqualityEdits.Valid (.editBelow entries))
    (laws : All (LeafLaw call condition holds ambient) (.editBelow entries))
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    ∀ terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ Forest condition entries index terms :=
  (all_exact call condition holds ambient).2.1 entries index values before results after trace valid laws semantic available closed

/-- Actual row scans retain their full original alternative language with the below-node condition. -/
theorem rows_exact {entries edges before results after}
    (trace : EditRows call entries edges before results after) (valid : SourceEqualityEdits.Valid (.editBelow entries))
    (laws : All (LeafLaw call condition holds ambient) (.editBelow entries))
    (semantic : SemanticReady before) (resident : Edges before edges) (closed : ClosedEdges edges) :
    ∀ term, (∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) ↔
      ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches condition (.editBelow entries) term :=
  (all_exact call condition holds ambient).2.2 entries edges before results after trace valid laws semantic resident closed

end MicroCFTA.SourceEqualityEditLanguage
