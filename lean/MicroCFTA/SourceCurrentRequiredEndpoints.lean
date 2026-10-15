import MicroCFTA.SourceCurrentRequiredResultPreservation
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Original path endpoints after actual required-path rebuilding

Each original full path retains its own gate certificate. Its demanded
trie lookup selects the actual child request. This applies even when the
path is a shorter prefix of another input path. No certificate for an
arbitrary prefix is inferred from a maximal tip.
-/
namespace MicroCFTA.SourceCurrentRequiredEndpoints
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityNeededNonnegative SourceEqualityRequiredGraph
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentRequiredSupport SourceCurrentRequiredLanguageEffects
open SourceCurrentSecondaryProjectionSupport (Support)
open SourceEqualityProjectionPathDomain (NodeClosed ForestClosed RowsClosed)
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- Every available closed value has the existing selected-path domain at every finite path. -/
theorem closed_path [DecidableEq (EdgeKey Symbol Guard)]
    (path : List Int) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (available : Available state value) (closed : value.free = []) : NodeClosed path value := by
  induction path generalizing value with
  | nil => simpa only [NodeClosed] using closed
  | cons index path ih =>
      cases value with
      | empty => simp only [NodeClosed]
      | reference | union | mu => simpa only [NodeClosed] using closed
      | node entry edges depth free =>
          rw [NodeClosed]
          intro edge member child selected
          have childClosed := MergedColdReaderClosed.node_children_closed state semantic.ready.semantic.1.normal.facts
            entry edges depth free available closed edge member child (SourceEqualityProjectionGraph.select_member selected)
          have childAvailable := available.children child (List.mem_flatMap.mpr
            ⟨edge, member, SourceEqualityProjectionGraph.select_member selected⟩)
          exact ih child childAvailable childClosed

private theorem select_natural (values : List A) (index : Nat) :
    SourceEqualityProjectionGraph.select values (Int.ofNat index) = values[index]? := by
  simp only [SourceEqualityProjectionGraph.select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl

private theorem makeNode_path [DecidableEq (EdgeKey Symbol Guard)]
    (index : Int) (path : List Int) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (resident : Edges state edges) (domain : RowsClosed path index edges) :
    NodeClosed (index :: path) (run (makeNode edges) state).1 := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary edges state facts resident
  generalize same : (run (makeNode edges) state).1 = value at ordinary ⊢
  cases value with
  | empty => simp only [NodeClosed]
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
      rw [NodeClosed]
      intro edge member child selected
      have origin : edge ∈ edges := by
        have present : edge ∈ InternedEdgeResidency.nodeEdges (run (makeNode edges) state).1 := by
          rw [same]
          exact member
        rw [EqualityLeafProjectionPhysical.makeNode_edges edges state facts.coherent facts.linked resident] at present
        exact (List.mem_filter.mp (canonicalEdges_member _ edge present)).1
      exact domain edge origin child selected

private def ChildEndpoints [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) : Prop :=
  ∀ index needed, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed →
    ∀ {value result : Value Symbol Guard} {before after}, RequireNode needed value before result after →
      SemanticReady before → Available before value → Grows anchor before → NodeSupport unconstrained anchor needed value →
      ∀ path : EqualityNormalize.Path, demands needed (path.map Int.ofNat) = true →
        Support unconstrained anchor path value → NodeClosed (path.map Int.ofNat) result

private theorem children_endpoint [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildEndpoints unconstrained anchor entries)
    {offset : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries offset values before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ChildrenSupport unconstrained anchor entries offset values)
    (query : Nat) (needed : Needed)
    (found : SourceEqualityNeededMap.lookup (Int.ofNat (offset + query)) entries = some needed)
    (path : EqualityNormalize.Path) (required : demands needed (path.map Int.ofNat) = true)
    (full : ∀ value, values[query]? = some value → Support unconstrained anchor path value) :
    ∀ result, results[query]? = some result → NodeClosed (path.map Int.ofNat) result := by
  induction values generalizing offset results before after query with
  | nil => cases trace; intro result selected; cases selected
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have restAvailable : Values before values := fun child member => available child (List.mem_cons_of_mem _ member)
      cases trace with
      | unselected offset absent rest =>
          cases query with
          | zero =>
              have absent : SourceEqualityNeededMap.lookup (Int.ofNat (offset + 0)) entries = none := by simpa using absent
              rw [absent] at found
              cases found
          | succ query =>
              exact ih rest semantic restAvailable growth (children_tail support) query
                (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) full
      | selected offset selected first rest =>
          have member := SourceEqualityNeededMap.lookup_mem _ entries _ selected
          have childValid := (show SourceEqualityNeededMap.Ascending entries ∧
            ∀ key child, (key, child) ∈ entries → SourceEqualityNeeded.Valid child from
            by simpa only [SourceEqualityNeeded.Valid] using valid).2 _ _ member
          have childNonnegative := (show ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child from
            by simpa only [Nonnegative] using nonnegative) _ _ member
          have firstSupport := support 0 _ (by simpa using selected) value rfl
          obtain ⟨firstKept, middleSemantic, _⟩ := SourceCurrentRequiredComplete.node_verified unconstrained anchor
            anchorSemantic first childValid childNonnegative.2 semantic firstAvailable growth firstSupport
          cases query with
          | zero =>
              have equal := Option.some.inj (selected.symm.trans
                (by simpa only [Nat.add_zero, Int.ofNat_eq_natCast] using found))
              cases equal
              intro result selectedResult
              have same := Option.some.inj selectedResult
              subst result
              exact laws offset _ (by simpa using selected) first semantic firstAvailable growth firstSupport
                path required (full value rfl)
          | succ query =>
              exact ih rest middleSemantic
                (fun child member => firstKept.available _ (restAvailable child member))
                (grows_trans growth firstKept.growth) (children_tail support) query
                (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) full

private theorem rows_endpoint [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildEndpoints unconstrained anchor entries)
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows entries edges before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (support : RowsSupport unconstrained anchor (.node entries) edges)
    (index : Nat) (needed : Needed) (found : SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed)
    (path : EqualityNormalize.Path) (required : demands needed (path.map Int.ofNat) = true)
    (full : ∀ edge ∈ edges, ∀ value, edge.children[index]? = some value → Support unconstrained anchor path value) :
    RowsClosed (path.map Int.ofNat) (Int.ofNat index) results := by
  induction edges generalizing results before after with
  | nil => cases trace; intro edge member; cases member
  | cons edge edges ih =>
      have restResident : Edges before edges := fun original member => resident original (List.mem_cons_of_mem _ member)
      have restSupport : RowsSupport unconstrained anchor (.node entries) edges :=
        fun original member => support original (List.mem_cons_of_mem _ member)
      have restFull := fun original member => full original (List.mem_cons_of_mem _ member)
      cases trace with
      | rejected doesNotFit rest => exact ih rest semantic restResident growth restSupport restFull
      | @kept _ _ values middle result afterEdge _ _ _ _ doesFit children rebuilt rest =>
          have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self)
          have childSupport : ChildrenSupport unconstrained anchor entries 0 edge.children := by
            simpa only [ChildrenSupport, ForestSupport, Nat.zero_add] using support edge List.mem_cons_self
          have firstDomain := children_endpoint anchorSemantic laws children valid nonnegative semantic available growth childSupport
            index needed (by simpa using found) path required (full edge List.mem_cons_self)
          obtain ⟨childKept, middleSemantic, valuesAvailable⟩ := children_verified unconstrained anchor anchorSemantic
            children valid nonnegative semantic available growth childSupport
          have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values
            middle middleSemantic.ready valuesAvailable
          have fields : result.children = values := by simpa only [rebuilt] using built.2.2
          have edgeKept : Keeps middle afterEdge := by simpa only [rebuilt] using built.1
          have afterSemantic : SemanticReady afterEdge := by
            simpa only [rebuilt] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol
              edge.entry.key.constraint values middle middleSemantic valuesAvailable
          have firstKept := childKept.trans edgeKept
          have tailDomain := ih rest afterSemantic
            (fun original member => InternedEdgeResidency.edge_grows before afterEdge firstKept.growth original
              (restResident original member)) (grows_trans growth firstKept.growth) restSupport restFull
          intro original member child selected
          rcases List.mem_cons.mp member with rfl | member
          · rw [fields, select_natural] at selected
            exact firstDomain child selected
          · exact tailDomain original member child selected

private theorem ordinary_endpoint [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildEndpoints unconstrained anchor entries)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode (.node entries) value before result after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (support : RowsSupport unconstrained anchor (.node entries) (InternedEdgeResidency.nodeEdges value))
    (index : Nat) (needed : Needed) (found : SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed)
    (path : EqualityNormalize.Path) (required : demands needed (path.map Int.ofNat) = true)
    (full : ∀ edge ∈ InternedEdgeResidency.nodeEdges value, ∀ child,
      edge.children[index]? = some child → Support unconstrained anchor path child) :
    NodeClosed ((index :: path).map Int.ofNat) result := by
  cases trace with
  | identity => simp [SourceEqualityNeededMap.lookup] at found
  | empty => simp only [List.map_cons, NodeClosed]
  | @ordinary entries edges before rebuilt middle result after entry depth free nonempty rows built =>
      have resident : Edges before edges := InternedEdgeResidency.resident_edges before
        semantic.ready.semantic.1.normal.facts.linked _ available.resident
      have domain := rows_endpoint anchorSemantic laws rows valid nonnegative semantic resident growth support
        index needed found path required full
      obtain ⟨_, middleSemantic, residentRows⟩ := rows_verified unconstrained anchor anchorSemantic
        rows valid nonnegative semantic resident growth support
      simpa only [List.map_cons, built] using makeNode_path (Int.ofNat index) (path.map Int.ofNat) rebuilt
        middle middleSemantic.ready.semantic.1.normal.facts residentRows domain
  | recursive nonempty recursive head body =>
      cases value <;> simp only [Recursive, SourceEqualityRequiredCache.Ordinary] at recursive ordinary

/-- Every demanded original full certificate derives the result's selected-path domain. -/
theorem node_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (needed : Needed) (valid : SourceEqualityNeeded.Valid needed) (nonnegative : Nonnegative needed)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value)
    (path : EqualityNormalize.Path) (required : demands needed (path.map Int.ofNat) = true)
    (certificate : Support unconstrained anchor path value) : NodeClosed (path.map Int.ofNat) result := by
  cases shape : needed with
  | node entries =>
      rw [shape] at trace support required
      have validEntries : SourceEqualityNeededMap.Ascending entries ∧
          ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
        simpa only [shape, SourceEqualityNeeded.Valid] using valid
      have nonnegativeEntries : ∀ index child, (index, child) ∈ entries → 0 ≤ index ∧ Nonnegative child := by
        simpa only [shape, Nonnegative] using nonnegative
      have laws : ChildEndpoints unconstrained anchor entries := by
        intro index child found value result before after actual semantic available growth support
        have member := SourceEqualityNeededMap.lookup_mem (Int.ofNat index) entries child found
        exact node_closed unconstrained anchor anchorSemantic anchorReady child (validEntries.2 _ _ member)
          (nonnegativeEntries _ _ member).2 actual semantic available growth support
      have checkedValid : SourceEqualityNeeded.Valid (.node entries) := by simpa only [shape] using valid
      have checkedNonnegative : Nonnegative (.node entries) := by simpa only [shape] using nonnegative
      cases path with
      | nil =>
          have closed := SourceCurrentSecondaryEndpointClosed.support_closed unconstrained anchor anchorReady value certificate
          simpa only [List.map_nil, NodeClosed] using
            (SourceEqualityRequiredExecution.node_verified trace semantic.ready available closed).2.2
      | cons index path =>
          rcases certificate with closed | ⟨resident, gate⟩
          · have checked := SourceCurrentRequiredComplete.node_verified unconstrained anchor anchorSemantic trace
              checkedValid checkedNonnegative semantic available growth support
            exact closed_path _ _ _ checked.2.1 checked.2.2
              (SourceEqualityRequiredExecution.node_verified trace semantic.ready available closed).2.2
          · cases found : SourceEqualityNeededMap.lookup (Int.ofNat index) entries with
            | none => simp only [List.map_cons, demands, found, Bool.false_eq_true] at required
            | some child =>
                have requested : demands child (path.map Int.ofNat) = true := by
                  simpa only [List.map_cons, demands, found] using required
                cases trace with
                | identity => simp [SourceEqualityNeededMap.lookup] at found
                | empty => simp only [List.map_cons, NodeClosed]
                | ordinary nonempty rows built =>
                    exact ordinary_endpoint anchorSemantic laws (.ordinary nonempty rows built)
                      checkedValid checkedNonnegative semantic available growth True.intro
                      (ordinary_rows support anchorSemantic semantic available) index child found path requested
                      (fun edge member value selected =>
                        SourceCurrentSecondaryProjectionSupport.ordinary_selected_support (Or.inr ⟨resident, gate⟩)
                          anchorSemantic semantic available edge member value selected)
                | recursive nonempty recursive head body =>
                    obtain ⟨exposed, middle, complete, kept, middleSemantic, exposedAvailable, ordinary, rows, _⟩ :=
                      SourceCurrentRequiredSupport.head_complete support nonempty checkedValid checkedNonnegative
                        anchorSemantic semantic available growth
                    obtain ⟨sameValue, sameState⟩ := complete.unique head
                    cases sameValue
                    cases sameState
                    exact ordinary_endpoint anchorSemantic laws body checkedValid checkedNonnegative
                      middleSemantic exposedAvailable (grows_trans growth kept.growth) ordinary rows
                      index child found path requested
                      (SourceCurrentSecondaryProjectionSupport.head_selected_support gate anchorSemantic resident
                        semantic available growth head)
termination_by sizeOf needed
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Actual requireAll retains each demanded original path's full selected-endpoint certificate. -/
theorem requireAll_path_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ForestSupport unconstrained anchor (build paths) values)
    (path : EqualityNormalize.Path) (nonroot : path ≠ []) (member : path.map Int.ofNat ∈ paths)
    (certificate : SourceCurrentSecondaryProjectionComplete.ForestSupport unconstrained anchor path values) :
    ForestClosed (path.map Int.ofNat) results := by
  have trace := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, done⟩
  have valid := build_valid paths
  have nonnegative := build_nonnegative paths indices
  have required := (demands_build paths (path.map Int.ofNat)).mpr (Or.inr ⟨_, member, ⟨[], by simp⟩⟩)
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at trace valid nonnegative required
      have weak : ChildrenSupport unconstrained anchor entries 0 values := by
        simpa only [ChildrenSupport, ForestSupport, compiled, Nat.zero_add] using support
      have validEntries : SourceEqualityNeededMap.Ascending entries ∧
          ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
        simpa only [SourceEqualityNeeded.Valid] using valid
      have nonnegativeEntries : ∀ index child, (index, child) ∈ entries → 0 ≤ index ∧ Nonnegative child := by
        simpa only [Nonnegative] using nonnegative
      have laws : ChildEndpoints unconstrained anchor entries := by
        intro index child found value result before after actual semantic available growth support
        have member := SourceEqualityNeededMap.lookup_mem _ entries child found
        exact node_closed unconstrained anchor anchorSemantic anchorReady child (validEntries.2 _ _ member)
          (nonnegativeEntries _ _ member).2 actual semantic available growth support
      cases path with
      | nil => exact False.elim (nonroot rfl)
      | cons index path =>
          cases found : SourceEqualityNeededMap.lookup (Int.ofNat index) entries with
          | none => simp only [List.map_cons, demands, found, Bool.false_eq_true] at required
          | some child =>
              have requested : demands child (path.map Int.ofNat) = true := by
                simpa only [List.map_cons, demands, found] using required
              have selected := children_endpoint anchorSemantic laws trace valid nonnegative semantic available growth weak
                index child (by simpa using found) path requested certificate
              intro value included
              exact selected value (by simpa only [select_natural] using included)

/-- Every original selected path retains its endpoint domain, including non-maximal prefixes. -/
theorem selected_paths_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (anchorAvailable : Values anchor values)
    (primary : ∀ paths ∈ selected,
      EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths anchor false anchor)
    (fuel readFuel : Nat) (results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths selected) values before = .done results after)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before) :
    ∀ path ∈ selected.flatten, path ≠ [] → ForestClosed (path.map Int.ofNat) results := by
  have tips := SourceCurrentRequiredTipSupport.selected_domain anchorSemantic anchorAvailable primary
  intro path included nonroot
  obtain ⟨paths, member, present⟩ := List.mem_flatten.mp included
  have gate := SourceCurrentSecondaryReplay.false_class_paths unconstrained values paths anchor anchor
    (SourceCurrentPrimaryProjectionSupport.class_false (primary paths member)) anchorSemantic anchorAvailable
    anchor (grows_refl anchor) path present
  have certificate := SourceCurrentSecondaryProjectionComplete.false_path_support gate nonroot anchorAvailable
  have encoded : path.map Int.ofNat ∈ SourceEqualitySelectedRequired.paths selected := List.mem_map.mpr
    ⟨path, (EqualityNormalize.mem_canonicalClass path selected.flatten).mpr (List.mem_flatten.mpr ⟨paths, member, present⟩), rfl⟩
  exact requireAll_path_closed unconstrained anchor anchorSemantic anchorReady fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) values results before after done
    (SourceEqualitySelectedRequired.paths_nonnegative selected) semantic available growth
    (SourceCurrentRequiredTipSupport.forest_support tips) path nonroot encoded certificate

end MicroCFTA.SourceCurrentRequiredEndpoints
