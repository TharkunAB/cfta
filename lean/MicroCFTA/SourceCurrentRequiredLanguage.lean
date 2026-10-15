import MicroCFTA.SourceCurrentRequiredLanguageEffects

/-!
# Exact requireAll language on the maximal-tip domain

Actual selected child calls, row filtering, and constructor readback derive
the exact required-path filter. Recursive heads supply their exposed row
domains and exact language. No whole-forest closedness or later support
premise is supplied. The finite worker keeps its existing macro-step bounds.
-/
namespace MicroCFTA.SourceCurrentRequiredLanguage
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityNeededMeaning SourceEqualityNeededNonnegative
open SourceEqualityRequiredCache SourceEqualityRequiredGraph SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredForestMeaning SourceCurrentRequiredSupport SourceCurrentRequiredLanguageEffects
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

private def ChildLaws [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) : Prop :=
  ∀ index needed, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed →
    ∀ {value result : Value Symbol Guard} {before after}, RequireNode needed value before result after →
      SemanticReady before → Available before value → Grows anchor before → NodeSupport unconstrained anchor needed value →
      ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches needed term

private theorem children_exact_aux [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildLaws unconstrained anchor entries)
    {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ChildrenSupport unconstrained anchor entries index values) :
    ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ Required entries index terms := by
  induction values generalizing index results before after with
  | nil =>
      cases trace
      intro holds ambient terms
      cases terms with
      | nil => exact ⟨fun accepted => ⟨accepted, trivial⟩, fun accepted => accepted.1⟩
      | cons => constructor <;> intro impossible <;> cases impossible <;> contradiction
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have restAvailable : Values before values := fun child member => available child (List.mem_cons_of_mem _ member)
      cases trace with
      | unselected index absent rest =>
          have tailExact := ih rest semantic restAvailable growth (children_tail support)
          intro holds ambient terms
          cases terms with
          | nil => constructor <;> intro impossible <;> cases impossible <;> contradiction
          | cons term terms =>
              constructor
              · intro accepted
                cases accepted with
                | cons first rest =>
                    obtain ⟨original, required⟩ := (tailExact holds ambient terms).mp rest
                    refine ⟨.cons first original, ?_, required⟩
                    intro needed found
                    rw [absent] at found
                    cases found
              · rintro ⟨original, required⟩
                cases original with
                | cons first rest => exact .cons first ((tailExact holds ambient terms).mpr ⟨rest, required.2⟩)
      | selected index found first rest =>
          have member := SourceEqualityNeededMap.lookup_mem _ entries _ found
          have childValid := (show SourceEqualityNeededMap.Ascending entries ∧
            ∀ key child, (key, child) ∈ entries → SourceEqualityNeeded.Valid child from
            by simpa only [SourceEqualityNeeded.Valid] using valid).2 _ _ member
          have childNonnegative := (show ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child from
            by simpa only [Nonnegative] using nonnegative) _ _ member
          have firstSupport := support 0 _ (by simpa using found) value rfl
          obtain ⟨firstKept, middleSemantic, _⟩ := SourceCurrentRequiredComplete.node_verified unconstrained anchor
            anchorSemantic first childValid childNonnegative.2 semantic firstAvailable growth firstSupport
          have tailExact := ih rest middleSemantic
            (fun child member => firstKept.available _ (restAvailable child member))
            (grows_trans growth firstKept.growth) (children_tail support)
          have firstExact := laws index _ found first semantic firstAvailable growth firstSupport
          intro holds ambient terms
          cases terms with
          | nil => constructor <;> intro impossible <;> cases impossible <;> contradiction
          | cons term terms =>
              constructor
              · intro accepted
                cases accepted with
                | cons initial rest =>
                    obtain ⟨originalFirst, matched⟩ := (firstExact holds ambient term).mp initial
                    obtain ⟨originalRest, required⟩ := (tailExact holds ambient terms).mp rest
                    refine ⟨.cons originalFirst originalRest, ?_, required⟩
                    intro child selected
                    exact Option.some.inj (found.symm.trans selected) ▸ matched
              · rintro ⟨original, required⟩
                cases original with
                | cons initial rest =>
                    exact .cons ((firstExact holds ambient term).mpr ⟨initial, required.1 _ found⟩)
                      ((tailExact holds ambient terms).mpr ⟨rest, required.2⟩)

private theorem rows_exact_aux [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildLaws unconstrained anchor entries)
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows entries edges before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (support : RowsSupport unconstrained anchor (.node entries) edges) :
    ∀ holds ambient term, (∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) ↔
      ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches (.node entries) term := by
  induction edges generalizing results before after with
  | nil =>
      cases trace
      intro holds ambient term
      simp
  | cons edge edges ih =>
      have restResident : Edges before edges := fun original member => resident original (List.mem_cons_of_mem _ member)
      have restSupport : RowsSupport unconstrained anchor (.node entries) edges :=
        fun original member => support original (List.mem_cons_of_mem _ member)
      cases trace with
      | rejected doesNotFit rest =>
          intro holds ambient term
          rw [ih rest semantic restResident growth restSupport holds ambient term]
          constructor
          · rintro ⟨original, member, accepted⟩
            exact ⟨original, List.mem_cons_of_mem _ member, accepted⟩
          · rintro ⟨original, member, accepted, matched⟩
            rcases List.mem_cons.mp member with rfl | member
            · obtain ⟨terms, shape, runs, _⟩ := accepted
              have doesFit := matching_row_fits (.node entries) valid original.entry.key.symbol terms
                (by simpa only [shape] using matched)
              rw [← runs.length_eq, doesNotFit] at doesFit
              cases doesFit
            · exact ⟨original, member, accepted, matched⟩
      | @kept _ _ values middle result afterEdge _ _ _ _ doesFit children rebuilt rest =>
          have allNonnegative : ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child := by
            simpa only [Nonnegative] using nonnegative
          have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self)
          have childSupport : ChildrenSupport unconstrained anchor entries 0 edge.children := by
            simpa only [ChildrenSupport, ForestSupport, Nat.zero_add] using support edge List.mem_cons_self
          obtain ⟨childKept, middleSemantic, valuesAvailable⟩ := children_verified unconstrained anchor anchorSemantic
            children valid nonnegative semantic available growth childSupport
          have edgeChecked := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values
            middle middleSemantic.ready valuesAvailable
          have afterSemantic : SemanticReady afterEdge := by
            simpa only [rebuilt] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol
              edge.entry.key.constraint values middle middleSemantic valuesAvailable
          have edgeKept : Keeps middle afterEdge := by simpa only [rebuilt] using edgeChecked.1
          have firstKept := childKept.trans edgeKept
          have tailExact := ih rest afterSemantic
            (fun original member => InternedEdgeResidency.edge_grows before afterEdge firstKept.growth original
              (restResident original member)) (grows_trans growth firstKept.growth) restSupport
          have childExact := children_exact_aux anchorSemantic laws children valid nonnegative semantic available growth childSupport
          have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleSemantic.ready.semantic.1.normal.facts
            edge.entry.key.symbol edge.entry.key.constraint values valuesAvailable
          have actualFields : result.entry.key.symbol = edge.entry.key.symbol ∧
              result.entry.key.constraint = edge.entry.key.constraint ∧ result.children = values := by
            simpa only [rebuilt] using fields
          intro holds ambient term
          have firstExact : EdgeMeaning (meaning holds ambient) holds result term ↔
              EdgeMeaning (meaning holds ambient) holds edge term ∧ Matches (.node entries) term := by
            unfold EdgeMeaning
            rw [actualFields.1, actualFields.2.1, actualFields.2.2]
            constructor
            · rintro ⟨terms, shape, runs, guard⟩
              have original := (checked_exact (meaning holds ambient) entries valid
                (fun key child member => (allNonnegative key child member).1) edge.children edge.entry.key.symbol terms doesFit).mp
                  ((childExact holds ambient terms).mp runs)
              exact ⟨⟨terms, shape, original.1, guard⟩, by simpa only [shape] using original.2⟩
            · rintro ⟨⟨terms, shape, runs, guard⟩, matched⟩
              have required := (checked_exact (meaning holds ambient) entries valid
                (fun key child member => (allNonnegative key child member).1) edge.children edge.entry.key.symbol terms doesFit).mpr
                  ⟨runs, by simpa only [shape] using matched⟩
              exact ⟨terms, shape, (childExact holds ambient terms).mpr required, guard⟩
          constructor
          · rintro ⟨output, member, accepted⟩
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨edge, List.mem_cons_self, firstExact.mp accepted⟩
            · obtain ⟨original, member, accepted⟩ := (tailExact holds ambient term).mp ⟨output, member, accepted⟩
              exact ⟨original, List.mem_cons_of_mem _ member, accepted⟩
          · rintro ⟨original, member, accepted⟩
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨result, List.mem_cons_self, firstExact.mpr accepted⟩
            · obtain ⟨output, member, accepted⟩ := (tailExact holds ambient term).mpr ⟨original, member, accepted⟩
              exact ⟨output, List.mem_cons_of_mem _ member, accepted⟩

private theorem ordinary_exact [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    (anchorSemantic : SemanticReady anchor) {entries : List (Int × Needed)}
    (laws : ChildLaws unconstrained anchor entries)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode (.node entries) value before result after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (ordinary : Ordinary value)
    (support : RowsSupport unconstrained anchor (.node entries) (InternedEdgeResidency.nodeEdges value)) :
    ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches (.node entries) term := by
  cases trace with
  | identity =>
      intro holds ambient term
      exact ⟨fun accepted => ⟨accepted, matches_empty term⟩, fun accepted => accepted.1⟩
  | empty => intro holds ambient term; simp only [meaning, false_and]
  | @ordinary entries edges before rebuilt middle result after entry depth free nonempty rows built =>
      have resident : Edges before edges := InternedEdgeResidency.resident_edges before
        semantic.ready.semantic.1.normal.facts.linked _ available.resident
      obtain ⟨_, middleSemantic, residentRows⟩ := rows_verified unconstrained anchor anchorSemantic
        rows valid nonnegative semantic resident growth support
      intro holds ambient term
      have actual := MergedColdInterpretation.makeNode_exact middle middleSemantic.ready.semantic.1.normal.facts
        (meaning holds ambient) rebuilt residentRows holds (InternedGuardedLanguage.laws holds ambient) term
      have readback : meaning holds ambient result term ↔
          ∃ edge ∈ rebuilt, EdgeMeaning (meaning holds ambient) holds edge term := by simpa only [built] using actual
      rw [readback, rows_exact_aux anchorSemantic laws rows valid nonnegative semantic resident growth support holds ambient term,
        (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term]
      constructor
      · rintro ⟨source, member, accepted, matched⟩
        exact ⟨⟨source, member, accepted⟩, matched⟩
      · rintro ⟨⟨source, member, accepted⟩, matched⟩
        exact ⟨source, member, accepted, matched⟩
  | recursive nonempty recursive head body =>
      cases value <;> simp only [Recursive, SourceEqualityRequiredCache.Ordinary] at recursive ordinary

/-- Actual supported node requests accept exactly the original terms that match their Needed trie. -/
theorem node_exact [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (needed : Needed) (valid : SourceEqualityNeeded.Valid needed) (nonnegative : Nonnegative needed)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) :
    ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches needed term := by
  cases shape : needed with
  | node entries =>
      rw [shape] at trace support
      have validEntries : SourceEqualityNeededMap.Ascending entries ∧
          ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
        simpa only [shape, SourceEqualityNeeded.Valid] using valid
      have nonnegativeEntries : ∀ index child, (index, child) ∈ entries → 0 ≤ index ∧ Nonnegative child := by
        simpa only [shape, Nonnegative] using nonnegative
      have laws : ChildLaws unconstrained anchor entries := by
        intro index child found value result before after actual semantic available growth support
        have member := SourceEqualityNeededMap.lookup_mem (Int.ofNat index) entries child found
        exact node_exact unconstrained anchor anchorSemantic child (validEntries.2 _ _ member)
          (nonnegativeEntries _ _ member).2 actual semantic available growth support
      have checkedValid : SourceEqualityNeeded.Valid (.node entries) := by simpa only [shape] using valid
      have checkedNonnegative : Nonnegative (.node entries) := by simpa only [shape] using nonnegative
      have checkedSupport : NodeSupport unconstrained anchor (.node entries) value := support
      cases trace with
      | identity =>
          intro holds ambient term
          exact ⟨fun accepted => ⟨accepted, matches_empty term⟩, fun accepted => accepted.1⟩
      | empty => intro holds ambient term; simp only [meaning, false_and]
      | ordinary nonempty rows built =>
          exact ordinary_exact anchorSemantic laws (.ordinary nonempty rows built) checkedValid checkedNonnegative
            semantic available growth True.intro (ordinary_rows checkedSupport anchorSemantic semantic available)
      | recursive nonempty recursive head body =>
          obtain ⟨exposed, middle, complete, kept, middleSemantic, resident, ordinary, rows, language⟩ :=
            SourceCurrentRequiredSupport.head_complete checkedSupport nonempty checkedValid checkedNonnegative
              anchorSemantic semantic available growth
          obtain ⟨sameValue, sameState⟩ := complete.unique head
          cases sameValue
          cases sameState
          intro holds ambient term
          rw [ordinary_exact anchorSemantic laws body checkedValid checkedNonnegative middleSemantic resident
            (grows_trans growth kept.growth) ordinary rows holds ambient term, language holds ambient term]
termination_by sizeOf needed
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Actual supported child scans retain the exact conditional requirements at original positions. -/
theorem children_exact [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ChildrenSupport unconstrained anchor entries index values) :
    ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ Required entries index terms := by
  apply children_exact_aux anchorSemantic ?_ trace valid nonnegative semantic available growth support
  intro index child found value result before after actual semantic available growth support
  have member := SourceEqualityNeededMap.lookup_mem _ entries child found
  have childValid := (show SourceEqualityNeededMap.Ascending entries ∧
    ∀ key child, (key, child) ∈ entries → SourceEqualityNeeded.Valid child from
    by simpa only [SourceEqualityNeeded.Valid] using valid).2 _ _ member
  have childNonnegative := (show ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child from
    by simpa only [Nonnegative] using nonnegative) _ _ member
  exact node_exact unconstrained anchor anchorSemantic child childValid childNonnegative.2 actual semantic available growth support

/-- Every completed supported requireAll worker has exact independent conditional filter language. -/
theorem requireAll_done [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ForestSupport unconstrained anchor (build paths) values) :
    ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ SourceEqualityRequiredAPI.ForestRequired paths terms := by
  have trace := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, done⟩
  have valid := build_valid paths
  have nonnegative := build_nonnegative paths indices
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at trace valid nonnegative
      simpa only [SourceEqualityRequiredAPI.ForestRequired, compiled] using
        children_exact unconstrained anchor anchorSemantic trace valid nonnegative semantic available growth
          (by simpa only [ChildrenSupport, ForestSupport, compiled, Nat.zero_add] using support)

/-- A checked root arity turns the conditional filter into existence of every complete source path. -/
theorem requireAll_paths [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index) (rootFits : fits (build paths) values.length = true)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ForestSupport unconstrained anchor (build paths) values) :
    ∀ holds ambient symbol terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧
        ∀ path ∈ paths, ∃ part, SymbolicSignedPaths.lookup (.node symbol terms) path = some part := by
  intro holds ambient symbol terms
  rw [requireAll_done unconstrained anchor anchorSemantic fuel readFuel paths values results before after done
    indices semantic available growth support holds ambient terms, ← build_exact]
  have valid := build_valid paths
  have nonnegative := build_nonnegative paths indices
  cases compiled : build paths with
  | node entries =>
      simp only [SourceEqualityRequiredAPI.ForestRequired, compiled] at valid nonnegative rootFits ⊢
      have keys : ∀ key child, (key, child) ∈ entries → 0 ≤ key := by
        rw [Nonnegative] at nonnegative
        exact fun key child member => (nonnegative key child member).1
      exact checked_exact (meaning holds ambient) entries valid keys values symbol terms rootFits

/-- Requiring supported paths preserves every accepted original forest in which those paths exist. -/
theorem requireAll_keep [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ForestSupport unconstrained anchor (build paths) values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (accepted : All₂ (meaning holds ambient) values terms)
    (pathsExist : ∀ path ∈ paths, ∃ part, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    All₂ (meaning holds ambient) results terms := by
  have matched := (build_exact paths (.node symbol terms)).mpr pathsExist
  have rootFits := matching_row_fits (build paths) (build_valid paths) symbol terms matched
  rw [← accepted.length_eq] at rootFits
  exact (requireAll_paths unconstrained anchor anchorSemantic fuel readFuel paths values results before after done
    indices rootFits semantic available growth support holds ambient symbol terms).mpr ⟨accepted, pathsExist⟩

/-- An actual primary false class derives finite exact requireAll filtering in each retained caller heap. -/
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
          (paths.map (List.map Int.ofNat)) values caller) results after ∧
      ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
        All₂ (meaning holds ambient) values terms ∧
          SourceEqualityRequiredAPI.ForestRequired (paths.map (List.map Int.ofNat)) terms := by
  have supported := primary_domain gate initialSemantic initialCosts initialAvailable
  have indices : ∀ path ∈ paths.map (List.map Int.ofNat), ∀ index ∈ path, 0 ≤ index := by
    intro path member index inside
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    obtain ⟨natural, _, rfl⟩ := List.mem_map.mp inside
    exact Int.natCast_nonneg natural
  obtain ⟨results, after, kept, afterSemantic, resident, stable⟩ :=
    SourceCurrentRequiredComplete.requireAll_complete unconstrained anchor supported.1
      (paths.map (List.map Int.ofNat)) indices values caller semantic available growth supported.2.2.2.2
  refine ⟨results, after, kept, afterSemantic, resident, stable, ?_⟩
  obtain ⟨fuel, readFuel, enough⟩ := stable
  exact requireAll_done unconstrained anchor supported.1 fuel readFuel (paths.map (List.map Int.ofNat))
    values results caller after (enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _))
      indices semantic available growth supported.2.2.2.2

end MicroCFTA.SourceCurrentRequiredLanguage
