import MicroCFTA.SourceEqualityRequiredHeadLanguage
import MicroCFTA.SourceEqualityRequiredSemanticEffects
import MicroCFTA.SourceEqualityRequiredForestMeaning
import MicroCFTA.SourceEqualityNeededNonnegative

/-!
# Exact independent language of the physical required-path graph

Actual head exposure, ordered child calls, row rejection, and constructor
readback derive the complete filter law. Every intermediate cache premise
comes from the physical graph. Symbols and full guards remain unchanged.
-/
namespace MicroCFTA.SourceEqualityRequiredLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityNeeded SourceEqualityNeededMeaning SourceEqualityNeededNonnegative
open SourceEqualityRequiredCache SourceEqualityRequiredGraph SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredListFacts SourceEqualityRequiredForestMeaning
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

private def NodeExact (needed : Needed) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) : Prop :=
  Valid needed → Nonnegative needed → SemanticReady before → Available before value → value.free = [] →
    ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches needed term

private def ChildrenExact (entries : List (Int × Needed)) (index : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) : Prop :=
  Valid (.node entries) → Nonnegative (.node entries) → SemanticReady before → Values before values → ClosedValues values →
    ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ Required entries index terms

private def RowsExact (entries : List (Int × Needed)) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) : Prop :=
  Valid (.node entries) → Nonnegative (.node entries) → SemanticReady before → Edges before edges → ClosedEdges edges →
    ∀ holds ambient term, (∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) ↔
      ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches (.node entries) term

private theorem all_exact [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode needed value before result after → NodeExact needed value before result) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      RequireChildren entries index values before results after → ChildrenExact entries index values before results) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows entries edges before results after → RowsExact entries edges before results) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeExact (.node []) value state value := by
    intro value state _ _ _ _ _ holds ambient term
    exact ⟨fun accepted => ⟨accepted, matches_empty term⟩, fun accepted => accepted.1⟩
  have emptyCase : ∀ {entries : List (Int × Needed)} {state}, entries ≠ [] →
      NodeExact (.node entries) (.empty : Value Symbol Guard) state .empty := by
    intro entries state _ _ _ _ _ _ holds ambient term
    simp only [meaning, false_and]
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (result, after) → RowsExact entries edges before rebuilt →
      NodeExact (.node entries) (.node entry edges depth free) before result := by
    intro entries edges before rebuilt middle result after entry depth free _ trace rebuiltEq rowsIH valid nonnegative semantic available closed holds ambient term
    have facts := semantic.ready.semantic.1.normal.facts
    have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have closedEdges := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have middleSemantic := SourceEqualityRequiredSemanticEffects.rows trace semantic resident closedEdges
    have checked := rows_verified trace semantic.ready resident closedEdges
    have actual := MergedColdInterpretation.makeNode_exact middle middleSemantic.ready.semantic.1.normal.facts
      (meaning holds ambient) rebuilt checked.2.1 holds (InternedGuardedLanguage.laws holds ambient) term
    have readback : meaning holds ambient result term ↔
        ∃ edge ∈ rebuilt, EdgeMeaning (meaning holds ambient) holds edge term := by simpa only [rebuiltEq] using actual
    rw [readback, rowsIH valid nonnegative semantic resident closedEdges holds ambient term,
      (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term]
    constructor
    · rintro ⟨edge, member, accepted, matched⟩
      exact ⟨⟨edge, member, accepted⟩, matched⟩
    · rintro ⟨⟨edge, member, accepted⟩, matched⟩
      exact ⟨edge, member, accepted, matched⟩
  have recursiveCase : ∀ {entries original before exposed middle result after},
      entries ≠ [] → Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeExact (.node entries) exposed middle result → NodeExact (.node entries) original before result := by
    intro entries original before exposed middle result after _ _ trace _ bodyIH valid nonnegative semantic available closed holds ambient term
    have nextSemantic := SourceEqualityRequiredSemanticCache.head trace semantic available closed
    have checked := trace.verified semantic.ready available closed
    rw [bodyIH valid nonnegative nextSemantic checked.2.1 checked.2.2.1 holds ambient term,
      SourceEqualityRequiredHeadLanguage.head_exact trace semantic available closed holds ambient term]
  have nilChildren : ∀ {entries index state}, ChildrenExact entries index ([] : List (Value Symbol Guard)) state [] := by
    intro entries index state _ _ _ _ _ holds ambient terms
    cases terms with
    | nil => exact ⟨fun accepted => ⟨accepted, trivial⟩, fun accepted => accepted.1⟩
    | cons term terms =>
        constructor
        · intro impossible; cases impossible
        · rintro ⟨impossible, _⟩; cases impossible
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenExact entries (index + 1) values before results → ChildrenExact entries index (value :: values) before (value :: results) := by
    intro entries values before results after value index absent _ restIH valid nonnegative semantic available closed holds ambient terms
    have tailExact := restIH valid nonnegative semantic
      (fun child member => available child (List.mem_cons_of_mem _ member))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) holds ambient
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
              intro needed found
              rw [absent] at found
              cases found
        · rintro ⟨original, required⟩
          cases original with
          | cons first rest => exact .cons first ((tailExact terms).mpr ⟨rest, required.2⟩)
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeExact needed value before result → ChildrenExact entries (index + 1) values middle results →
      ChildrenExact entries index (value :: values) before (result :: results) := by
    intro entries needed value before result middle values results after index found first _ firstIH restIH valid nonnegative semantic available closed holds ambient terms
    have member := SourceEqualityNeededMap.lookup_mem _ entries needed found
    have childValid : SourceEqualityNeeded.Valid needed := by
      have checked := valid
      rw [SourceEqualityNeeded.Valid] at checked
      exact checked.2 _ _ member
    have childNonnegative : Nonnegative needed := by
      have checked := nonnegative
      rw [Nonnegative] at checked
      exact (checked _ _ member).2
    have firstAvailable := available value List.mem_cons_self
    have firstClosed := closed value List.mem_cons_self
    have nextSemantic := SourceEqualityRequiredSemanticEffects.node first semantic firstAvailable firstClosed
    have checked := SourceEqualityRequiredExecution.node_verified first semantic.ready firstAvailable firstClosed
    have tailExact := restIH valid nonnegative nextSemantic
      (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) holds ambient
    have firstExact := firstIH childValid childNonnegative semantic firstAvailable firstClosed holds ambient
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
              exact .cons ((firstExact term).mpr ⟨initial, required.1 needed found⟩)
                ((tailExact terms).mpr ⟨rest, required.2⟩)
  have nilRows : ∀ {entries state}, RowsExact entries ([] : List (EdgeValue Symbol Guard)) state [] := by
    intro entries state _ _ _ _ _ holds ambient term
    simp
  have rejectedCase : ∀ {entries edges before results after edge},
      fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      RowsExact entries edges before results → RowsExact entries (edge :: edges) before results := by
    intro entries edges before results after edge doesNotFit _ restIH valid nonnegative semantic resident closed holds ambient term
    rw [restIH valid nonnegative semantic
      (fun original member => resident original (List.mem_cons_of_mem _ member))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) holds ambient term]
    constructor
    · rintro ⟨original, member, accepted⟩
      exact ⟨original, List.mem_cons_of_mem _ member, accepted⟩
    · rintro ⟨original, member, accepted, matched⟩
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨terms, shape, runs, _⟩ := accepted
        have doesFit := matching_row_fits (.node entries) valid original.entry.key.symbol terms (by simpa only [shape] using matched)
        rw [← runs.length_eq, doesNotFit] at doesFit
        cases doesFit
      · exact ⟨original, member, accepted, matched⟩
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenExact entries 0 edge.children before values → RowsExact entries edges afterEdge results →
      RowsExact entries (edge :: edges) before (result :: results) := by
    intro entries before values middle result afterEdge edges results after edge doesFit childTrace rebuilt _ childIH restIH valid nonnegative semantic resident closed holds ambient term
    have allNonnegative : ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child := by
      simpa only [Nonnegative] using nonnegative
    have facts := semantic.ready.semantic.1.normal.facts
    have available : Values before edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have middleSemantic := SourceEqualityRequiredSemanticEffects.children childTrace semantic available (closed edge List.mem_cons_self)
    have checked := children_verified childTrace semantic.ready available (closed edge List.mem_cons_self)
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic checked.2.1
    have edgeChecked := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic.ready checked.2.1
    have afterSemantic : SemanticReady afterEdge := by simpa only [rebuilt] using edgeSemantic
    have edgeKeeps : Keeps middle afterEdge := by simpa only [rebuilt] using edgeChecked.1
    have growth := (checked.1.trans edgeKeeps).growth
    have tailExact := restIH valid nonnegative afterSemantic
      (fun original member => InternedEdgeResidency.edge_grows before afterEdge growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) holds ambient term
    have childExact := childIH valid nonnegative semantic available (closed edge List.mem_cons_self) holds ambient
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleSemantic.ready.semantic.1.normal.facts
      edge.entry.key.symbol edge.entry.key.constraint values checked.2.1
    have actualFields : result.entry.key.symbol = edge.entry.key.symbol ∧
        result.entry.key.constraint = edge.entry.key.constraint ∧ result.children = values := by simpa only [rebuilt] using fields
    have firstExact : EdgeMeaning (meaning holds ambient) holds result term ↔
        EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches (.node entries) term := by
      unfold EdgeMeaning
      rw [actualFields.1, actualFields.2.1, actualFields.2.2]
      constructor
      · rintro ⟨terms, shape, runs, guard⟩
        have original := (checked_exact (meaning holds ambient) entries valid
          (fun key child member => (allNonnegative key child member).1) edge.children edge.entry.key.symbol terms doesFit).mp
          ((childExact terms).mp runs)
        exact ⟨⟨terms, shape, original.1, guard⟩, by simpa only [shape] using original.2⟩
      · rintro ⟨⟨terms, shape, runs, guard⟩, matched⟩
        have required := (checked_exact (meaning holds ambient) entries valid
          (fun key child member => (allNonnegative key child member).1) edge.children edge.entry.key.symbol terms doesFit).mpr
          ⟨runs, by simpa only [shape] using matched⟩
        exact ⟨terms, shape, (childExact terms).mpr required, guard⟩
    constructor
    · rintro ⟨output, member, accepted⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨edge, List.mem_cons_self, (firstExact.mp accepted)⟩
      · obtain ⟨original, member, accepted⟩ := tailExact.mp ⟨output, member, accepted⟩
        exact ⟨original, List.mem_cons_of_mem _ member, accepted⟩
    · rintro ⟨original, member, accepted⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨result, List.mem_cons_self, firstExact.mpr accepted⟩
      · obtain ⟨output, member, accepted⟩ := tailExact.mpr ⟨original, member, accepted⟩
        exact ⟨output, List.mem_cons_of_mem _ member, accepted⟩
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after trace
    exact RequireNode.rec
      (motive_1 := fun needed value before result _ _ => NodeExact needed value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenExact entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsExact entries edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries index values before results after trace
    exact RequireChildren.rec
      (motive_1 := fun needed value before result _ _ => NodeExact needed value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenExact entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsExact entries edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries edges before results after trace
    exact RequireRows.rec
      (motive_1 := fun needed value before result _ _ => NodeExact needed value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenExact entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsExact entries edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace

/-- Every completed node request accepts precisely the original terms that match its trie. -/
theorem node_exact [DecidableEq (EdgeKey Symbol Guard)]
    {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after) (valid : Valid needed) (nonnegative : Nonnegative needed)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches needed term :=
  all_exact.1 needed value before result after trace valid nonnegative semantic available closed

/-- Every completed child scan has the exact original-position forest meaning. -/
theorem children_exact [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after) (valid : Valid (.node entries))
    (nonnegative : Nonnegative (.node entries)) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ Required entries index terms :=
  all_exact.2.1 entries index values before results after trace valid nonnegative semantic available closed

/-- Every completed row scan retains the original alternatives with the full trie filter. -/
theorem rows_exact [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows entries edges before results after) (valid : Valid (.node entries))
    (nonnegative : Nonnegative (.node entries)) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    ∀ holds ambient term, (∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) ↔
      ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches (.node entries) term :=
  all_exact.2.2 entries edges before results after trace valid nonnegative semantic resident closed

end MicroCFTA.SourceEqualityRequiredLanguage
