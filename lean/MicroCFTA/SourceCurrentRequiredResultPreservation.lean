import MicroCFTA.SourceCurrentRequiredResultDomain

/-!
# Structural result domains through actual required-path graphs

Original terminal certificates derive closed unchanged endpoints. Selected
ordinary prefixes rebuild only from actual returned child domains. Recursive
heads supply the domains of their actual exposed rows. Constructor readback
retains child order and canonical row origins. No future result certificate
or closed-forest adapter is supplied.
-/
namespace MicroCFTA.SourceCurrentRequiredResultPreservation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityNeededNonnegative SourceEqualityRequiredGraph
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentRequiredTipSupport SourceCurrentRequiredResultDomain
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- Every selected original child retains all its stored tips at its actual list offset. -/
def ChildrenTips [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (offset : Nat) (values : List (Value Symbol Guard)) : Prop :=
  ∀ query needed, SourceEqualityNeededMap.lookup (Int.ofNat (offset + query)) entries = some needed →
    ∀ value, values[query]? = some value → NodeTips unconstrained anchor needed value

private theorem tips_tail [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    {entries : List (Int × Needed)} {offset : Nat} {value : Value Symbol Guard} {values : List (Value Symbol Guard)}
    (tips : ChildrenTips unconstrained anchor entries offset (value :: values)) :
    ChildrenTips unconstrained anchor entries (offset + 1) values := by
  intro query needed found child selected
  exact tips (query + 1) needed
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) child selected

private theorem tips_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    {entries : List (Int × Needed)} {offset : Nat} {values : List (Value Symbol Guard)}
    (tips : ChildrenTips unconstrained anchor entries offset values) :
    SourceCurrentRequiredLanguageEffects.ChildrenSupport unconstrained anchor entries offset values :=
  fun query needed found value selected => node_support (tips query needed found value selected)

private def ChildLaws [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) : Prop :=
  ∀ index needed, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed →
    ∀ {value result : Value Symbol Guard} {before after}, RequireNode needed value before result after →
      SemanticReady before → Available before value → Grows anchor before → NodeTips unconstrained anchor needed value →
      NodeDomain needed result

private theorem children_domain_aux [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildLaws unconstrained anchor entries)
    {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (tips : ChildrenTips unconstrained anchor entries index values) : ChildrenDomain entries index results := by
  induction values generalizing index results before after with
  | nil => cases trace; intro query needed found value selected; cases selected
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have restAvailable : Values before values := fun child member => available child (List.mem_cons_of_mem _ member)
      cases trace with
      | unselected index absent rest =>
          apply children_cons ?_ (ih rest semantic restAvailable growth (tips_tail tips))
          intro needed found
          have missing : SourceEqualityNeededMap.lookup (Int.ofNat index) entries = none := absent
          rw [missing] at found
          cases found
      | selected index found first rest =>
          have firstTips := tips 0 _ (by simpa using found) value rfl
          have firstDomain := laws index _ found first semantic firstAvailable growth firstTips
          have member := SourceEqualityNeededMap.lookup_mem _ entries _ found
          have childValid := (show SourceEqualityNeededMap.Ascending entries ∧
            ∀ key child, (key, child) ∈ entries → SourceEqualityNeeded.Valid child from
            by simpa only [SourceEqualityNeeded.Valid] using valid).2 _ _ member
          have childNonnegative := (show ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child from
            by simpa only [Nonnegative] using nonnegative) _ _ member
          obtain ⟨firstKept, middleSemantic, _⟩ := SourceCurrentRequiredComplete.node_verified unconstrained anchor
            anchorSemantic first childValid childNonnegative.2 semantic firstAvailable growth (node_support firstTips)
          apply children_cons ?_ (ih rest middleSemantic
            (fun child member => firstKept.available _ (restAvailable child member))
            (grows_trans growth firstKept.growth) (tips_tail tips))
          intro needed selected
          exact Option.some.inj (found.symm.trans selected) ▸ firstDomain

private theorem rows_domain_aux [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildLaws unconstrained anchor entries)
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows entries edges before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (tips : ∀ edge ∈ edges, ForestTips unconstrained anchor (.node entries) edge.children) :
    RowsDomain (.node entries) results := by
  induction edges generalizing results before after with
  | nil => cases trace; intro edge member; cases member
  | cons edge edges ih =>
      have restResident : Edges before edges := fun original member => resident original (List.mem_cons_of_mem _ member)
      have restTips := fun original member => tips original (List.mem_cons_of_mem _ member)
      cases trace with
      | rejected doesNotFit rest => exact ih rest semantic restResident growth restTips
      | @kept _ _ values middle result afterEdge _ _ _ _ doesFit children rebuilt rest =>
          have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self)
          have childTips : ChildrenTips unconstrained anchor entries 0 edge.children := by
            simpa only [ChildrenTips, ForestTips, Nat.zero_add] using tips edge List.mem_cons_self
          have childDomain := children_domain_aux anchorSemantic laws children valid nonnegative semantic available growth childTips
          obtain ⟨childKept, middleSemantic, valuesAvailable⟩ :=
            SourceCurrentRequiredLanguageEffects.children_verified unconstrained anchor anchorSemantic
              children valid nonnegative semantic available growth (tips_support childTips)
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
              (restResident original member)) (grows_trans growth firstKept.growth) restTips
          intro original member
          rcases List.mem_cons.mp member with rfl | member
          · rw [fields]
            simpa only [ForestDomain, ChildrenDomain, Nat.zero_add] using childDomain
          · exact tailDomain original member

private theorem ordinary_domain_aux [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildLaws unconstrained anchor entries) (nonempty : entries ≠ [])
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode (.node entries) value before result after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (tips : ∀ edge ∈ InternedEdgeResidency.nodeEdges value, ForestTips unconstrained anchor (.node entries) edge.children) :
    NodeDomain (.node entries) result := by
  cases trace with
  | identity => exact False.elim (nonempty rfl)
  | empty => exact .closed rfl
  | @ordinary entries edges before rebuilt middle result after entry depth free nonempty rows built =>
      have resident : Edges before edges := InternedEdgeResidency.resident_edges before
        semantic.ready.semantic.1.normal.facts.linked _ available.resident
      have domain := rows_domain_aux anchorSemantic laws rows valid nonnegative semantic resident growth tips
      obtain ⟨_, middleSemantic, residentRows⟩ := SourceCurrentRequiredLanguageEffects.rows_verified unconstrained anchor
        anchorSemantic rows valid nonnegative semantic resident growth
          (fun edge member => forest_support (tips edge member))
      simpa only [built] using makeNode_domain entries nonempty rebuilt middle
        middleSemantic.ready.semantic.1.normal.facts residentRows domain
  | recursive nonempty recursive head body =>
      cases value <;> simp only [Recursive, SourceEqualityRequiredCache.Ordinary] at recursive ordinary

/-- Actual supported node requests derive structural domains for their reconstructed outputs. -/
theorem node_domain [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (needed : Needed) (valid : SourceEqualityNeeded.Valid needed) (nonnegative : Nonnegative needed)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (tips : NodeTips unconstrained anchor needed value) : NodeDomain needed result := by
  cases shape : needed with
  | node entries =>
      rw [shape] at trace tips
      have validEntries : SourceEqualityNeededMap.Ascending entries ∧
          ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
        simpa only [shape, SourceEqualityNeeded.Valid] using valid
      have nonnegativeEntries : ∀ index child, (index, child) ∈ entries → 0 ≤ index ∧ Nonnegative child := by
        simpa only [shape, Nonnegative] using nonnegative
      have laws : ChildLaws unconstrained anchor entries := by
        intro index child found value result before after actual semantic available growth tips
        have member := SourceEqualityNeededMap.lookup_mem (Int.ofNat index) entries child found
        exact node_domain unconstrained anchor anchorSemantic anchorReady child (validEntries.2 _ _ member)
          (nonnegativeEntries _ _ member).2 actual semantic available growth tips
      have checkedValid : SourceEqualityNeeded.Valid (.node entries) := by simpa only [shape] using valid
      have checkedNonnegative : Nonnegative (.node entries) := by simpa only [shape] using nonnegative
      cases trace with
      | identity => exact .closed (empty_closed anchorReady tips)
      | empty => exact .closed rfl
      | ordinary nonempty rows built =>
          exact ordinary_domain_aux anchorSemantic laws nonempty (.ordinary nonempty rows built)
            checkedValid checkedNonnegative semantic available growth True.intro
              (SourceCurrentRequiredTipSupport.ordinary_rows tips anchorSemantic semantic available)
      | recursive nonempty recursive head body =>
          obtain ⟨exposed, middle, complete, kept, middleSemantic, resident, ordinary, _, _⟩ :=
            SourceCurrentRequiredSupport.head_complete (node_support tips) nonempty checkedValid checkedNonnegative
              anchorSemantic semantic available growth
          obtain ⟨sameValue, sameState⟩ := complete.unique head
          cases sameValue
          cases sameState
          exact ordinary_domain_aux anchorSemantic laws nonempty body checkedValid checkedNonnegative
            middleSemantic resident (grows_trans growth kept.growth) ordinary
              (head_rows tips anchorSemantic semantic available growth head)
termination_by sizeOf needed
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Actual child scans retain structural result domains at their original positions. -/
theorem children_domain [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (tips : ChildrenTips unconstrained anchor entries index values) : ChildrenDomain entries index results := by
  apply children_domain_aux anchorSemantic ?_ trace valid nonnegative semantic available growth tips
  intro index child found value result before after actual semantic available growth tips
  have member := SourceEqualityNeededMap.lookup_mem _ entries child found
  have childValid := (show SourceEqualityNeededMap.Ascending entries ∧
    ∀ key child, (key, child) ∈ entries → SourceEqualityNeeded.Valid child from
    by simpa only [SourceEqualityNeeded.Valid] using valid).2 _ _ member
  have childNonnegative := (show ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child from
    by simpa only [Nonnegative] using nonnegative) _ _ member
  exact node_domain unconstrained anchor anchorSemantic anchorReady child childValid childNonnegative.2
    actual semantic available growth tips

/-- Actual row filtering and rebuilding derive structural domains for every returned row. -/
theorem rows_domain [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows entries edges before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (tips : ∀ edge ∈ edges, ForestTips unconstrained anchor (.node entries) edge.children) :
    RowsDomain (.node entries) results := by
  apply rows_domain_aux anchorSemantic ?_ trace valid nonnegative semantic resident growth tips
  intro index child found value result before after actual semantic available growth tips
  have member := SourceEqualityNeededMap.lookup_mem _ entries child found
  have childValid := (show SourceEqualityNeededMap.Ascending entries ∧
    ∀ key child, (key, child) ∈ entries → SourceEqualityNeeded.Valid child from
    by simpa only [SourceEqualityNeeded.Valid] using valid).2 _ _ member
  have childNonnegative := (show ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child from
    by simpa only [Nonnegative] using nonnegative) _ _ member
  exact node_domain unconstrained anchor anchorSemantic anchorReady child childValid childNonnegative.2
    actual semantic available growth tips

/-- Completed requireAll returns its structural forest domain and exact actual semantic effects. -/
theorem requireAll_verified [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (tips : ForestTips unconstrained anchor (build paths) values) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ForestDomain (build paths) results := by
  have trace := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, done⟩
  have valid := build_valid paths
  have nonnegative := build_nonnegative paths indices
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at trace valid nonnegative
      have childTips : ChildrenTips unconstrained anchor entries 0 values := by
        simpa only [compiled, ChildrenTips, ForestTips, Nat.zero_add] using tips
      obtain ⟨kept, ready, resident⟩ := SourceCurrentRequiredLanguageEffects.children_verified unconstrained anchor
        anchorSemantic trace valid nonnegative semantic available growth (tips_support childTips)
      refine ⟨kept, ready, resident, ?_⟩
      simpa only [ForestDomain, ChildrenDomain, Nat.zero_add] using children_domain unconstrained anchor anchorSemantic
        anchorReady trace valid nonnegative semantic available growth childTips

end MicroCFTA.SourceCurrentRequiredResultPreservation
