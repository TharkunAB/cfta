import MicroCFTA.SourceCurrentMemoMergeLanguageContracts
import MicroCFTA.SourceMergedGroups

/-!
# Independent language certificates for memo-aware source bodies

Every source constructor uses its actual returned fields. Ordered maps
retain the input and result at each position. Recursive requests use the
stronger local contract. The actual Run and Call induction discharges that
contract separately. No uncached callback is substituted for a memo request.
-/
namespace MicroCFTA.SourceCurrentMemoMergeLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Certified Effect bind_certified)
open SourceMergedContracts (ValuePost EdgePost RowsPost)
open InternedGuardedLanguage (meaning Env)
open MergedColdInterpretation (EdgeMeaning)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Ordered traversal retains one certificate for each literal input position. -/
theorem paired_map_certified (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Request → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ request value, post before request value → post after request value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Certified (Contract holds ambient) clear (call request) before (fun after output => post after request output))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Certified (Contract holds ambient) clear (map call requests) before
      (fun after values => All₂ (post after) requests values) := by
  induction requests generalizing before with
  | nil => exact .nil
  | cons request requests ih =>
      apply bind_certified (Contract holds ambient) clear _ _ before (fun state output => post state request output) _
        (checked request List.mem_cons_self before semantic costs (inputs request List.mem_cons_self))
      intro value middle effect valid
      apply bind_certified (Contract holds ambient) clear _ _ middle _ _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready
      exact .cons (postGrows middle after later request value valid) ready

private theorem request_certified (clear : Guard → Bool) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (value : Value Symbol Guard) (before : State Symbol Guard) (available : Available before value) (closed : value.free = []) :
    Certified (Contract holds ambient) clear (.request value) before (fun after result => ValuePost holds ambient [value] after result) := by
  refine ⟨available, ?_⟩
  intro result after _ returned
  exact ⟨returned.1.1, returned.1.2 closed, fun original member term accepted =>
    returned.2 term (by simpa only [List.mem_singleton.mp member] using accepted)⟩

private theorem retained_certified (clear : Guard → Bool) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs) (closed : ClosedValues inputs) :
    Certified (Contract holds ambient) clear (retainedColumn inputs) before (ValuePost holds ambient inputs) := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values) :
      Certified (Contract holds ambient) clear
        (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
          else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) before (ValuePost holds ambient values) := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      refine ⟨⟨checked.1.1, checked.1.2,
        InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeUnion_noNewMu values before)⟩,
        checked.2.1, checked.2.2, ?_⟩
      intro value member term accepted
      exact (MergedColdInterpretation.makeUnion_common before semantic.ready.semantic.1.normal.facts
        (meaning holds ambient) values available holds (InternedGuardedLanguage.laws holds ambient) term).mpr ⟨value, member, accepted⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact holds ambient values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      apply bind_certified (Contract holds ambient) clear (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request before (ValuePost holds ambient values) _
        ⟨⟨checked.1.1, checked.1.2,
          InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu _ before)⟩,
          checked.2.1, checked.2.2.1, fun value member term accepted => (checked.2.2.2 term).mpr ⟨value, member, accepted⟩⟩
      intro value middle _ ready
      refine ⟨ready.available, ?_⟩
      intro result after _ returned
      exact ⟨returned.1.1, returned.1.2 ready.closed,
        fun original member term accepted => returned.2 term (ready.covers original member term accepted)⟩
  cases inputs with
  | nil => exact branches [] available closed
  | cons first rest =>
      cases rest with
      | nil => exact ⟨available first List.mem_cons_self, closed first List.mem_cons_self,
          fun original member term accepted => by simpa only [List.mem_singleton.mp member] using accepted⟩
      | cons second rest => exact branches (first :: second :: rest) available closed

private theorem column_certified (clear : Guard → Bool) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (_costs : CostHeap before) (available : Values before inputs) (closed : ClosedValues inputs) :
    Certified (Contract holds ambient) clear (column inputs) before (ValuePost holds ambient inputs) := by
  apply bind_certified (Contract holds ambient) clear _ _ before
    (fun state values => Values state values ∧ ClosedValues values ∧
      ∀ term, (∃ value ∈ values, meaning holds ambient value term) ↔ ∃ value ∈ inputs, meaning holds ambient value term) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done _
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel holds ambient clearTrue inputs before semantic available closed values after done
    exact ⟨checked.2.1, checked.2.2.1, checked.2.2.2.2⟩
  · intro values middle effect ready
    exact (retained_certified clear holds ambient values middle effect.semantic effect.costs ready.1 ready.2.1).mono (by
      intro after result returned
      refine ⟨returned.available, returned.closed, ?_⟩
      intro value member term accepted
      obtain ⟨kept, present, run⟩ := (ready.2.2 term).mpr ⟨value, member, accepted⟩
      exact returned.covers kept present term run)

private theorem small_certified (clear : Guard → Bool) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : EdgeResident before edge) (closed : ClosedValues edge.children) :
    Certified (Contract holds ambient) clear (small edge) before (EdgePost holds ambient [edge]) := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  apply bind_certified (Contract holds ambient) clear _ _ before
    (fun state values => All₂ (fun input result => ValuePost holds ambient [input] state result) edge.children values) _
    (paired_map_certified holds ambient clear Code.request (fun state value => Available state value ∧ value.free = [])
      (fun state input result => ValuePost holds ambient [input] state result)
      (fun _ _ effect value ready => ⟨effect.keeps.available value ready.1, ready.2⟩)
      (fun _ _ effect _ _ post => post.grows ⟨effect.keeps, effect.semantic⟩) edge.children
      (fun value _ state _ _ ready => request_certified clear holds ambient value state ready.1 ready.2)
      before semantic costs (fun value member => ⟨available value member, closed value member⟩))
  intro values middle effect ready
  have valuesAvailable : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.available))
  have valuesClosed : ClosedValues values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.closed))
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear edge.entry.key.symbol edge.entry.key.constraint values
    middle effect.semantic effect.costs valuesAvailable valuesClosed
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle effect.semantic.ready.semantic.1.normal.facts
    edge.entry.key.symbol edge.entry.key.constraint values valuesAvailable
  refine ⟨checked.1, checked.2.1, ?_, ?_⟩
  · rw [fields.2.2]; exact valuesClosed
  · intro original member term accepted
    rw [List.mem_singleton.mp member] at accepted
    obtain ⟨terms, same, runs, guard⟩ := accepted
    refine ⟨terms, ?_, ?_, ?_⟩
    · rw [fields.1]; exact same
    · rw [fields.2.2]
      exact SourceMergedColumns.covers_runs holds ambient (fun value => [value]) _ _ middle ready terms
        (runs.imp (fun value term accepted => ⟨value, List.mem_cons_self, accepted⟩))
    · rw [fields.2.1]; exact guard

private theorem large_certified (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) (keys : MergedPhysicalGroupEdges.SameKey (first :: rest))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest)) :
    Certified (Contract holds ambient) clear (large top first rest) before (EdgePost holds ambient (first :: rest)) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply bind_certified (Contract holds ambient) clear _ _ before
    (fun state values => All₂ (fun inputs result => ValuePost holds ambient inputs state result) columns values) _
    (paired_map_certified holds ambient clear column (fun state inputs => Values state inputs ∧ ClosedValues inputs)
      (fun state inputs result => ValuePost holds ambient inputs state result)
      (fun _ _ effect _ ready => ⟨(fun value member => effect.keeps.available value (ready.1 value member)), ready.2⟩)
      (fun _ _ effect _ _ post => post.grows ⟨effect.keeps, effect.semantic⟩) columns
      (fun values _ state semantic costs ready => column_certified clear holds ambient clearTrue values state semantic costs ready.1 ready.2)
      before semantic costs (fun column member => ⟨(by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact closed edge outer value inner)⟩))
  intro values middle effect ready
  have valuesAvailable : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.available))
  have valuesClosed : ClosedValues values := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.closed))
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear first.entry.key.symbol top values middle effect.semantic effect.costs valuesAvailable valuesClosed
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle effect.semantic.ready.semantic.1.normal.facts first.entry.key.symbol top values valuesAvailable
  refine ⟨checked.1, checked.2.1, ?_, ?_⟩
  · rw [fields.2.2]; exact valuesClosed
  · intro edge member term accepted
    obtain ⟨terms, same, runs, _⟩ := accepted
    have key := keys edge member first List.mem_cons_self
    refine ⟨terms, ?_, ?_, ?_⟩
    · rw [fields.1, ← key.1]; exact same
    · rw [fields.2.2]
      apply SourceMergedColumns.covers_runs holds ambient id columns values middle ready terms
      have covered := MergedAlternativesGroups.columns_cover (meaning holds ambient) ((first :: rest).map EdgeValue.children)
        edge.children terms (List.mem_map.mpr ⟨edge, member, rfl⟩) runs
      simpa only [key.2, id, columns] using covered
    · rw [fields.2.1]; exact topTrue term

private theorem group_certified (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (edges : List (EdgeValue Symbol Guard)) (keys : MergedPhysicalGroupEdges.SameKey edges)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    Certified (Contract holds ambient) clear (group top edges) before (RowsPost holds ambient edges) := by
  unfold group
  split
  · have checked := paired_map_certified holds ambient clear small
      (fun state edge => EdgeResident state edge ∧ ClosedValues edge.children)
      (fun state edge result => EdgePost holds ambient [edge] state result)
      (fun _ _ effect edge ready => ⟨InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge ready.1, ready.2⟩)
      (fun _ _ effect _ _ post => post.grows ⟨effect.keeps, effect.semantic⟩) edges
      (fun edge _ state semantic costs ready => small_certified clear holds ambient edge state semantic costs ready.1 ready.2)
      before semantic costs (fun edge member => ⟨resident edge member, closed edge member⟩)
    exact checked.mono (by
      intro state results ready
      refine ⟨EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.resident)),
        EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.closed)), ?_⟩
      intro edge member term accepted
      obtain ⟨result, included, post⟩ := SymbolicSmartRows.all₂_child _ _ _ ready edge member
      exact ⟨result, included, post.covers edge List.mem_cons_self term accepted⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply bind_certified (Contract holds ambient) clear _ _ before (EdgePost holds ambient (first :: rest)) _
          (large_certified clear top holds ambient clearTrue topTrue first rest keys before semantic costs resident closed)
        intro result _ _ ready
        exact ⟨(fun edge member => by rw [List.mem_singleton.mp member]; exact ready.resident),
          (fun edge member => by rw [List.mem_singleton.mp member]; exact ready.closed),
          fun edge member term accepted => ⟨result, List.mem_cons_self, ready.covers edge member term accepted⟩⟩

private theorem root_certified (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (edges : List (EdgeValue Symbol Guard)) (groups : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges groups)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    Certified (Contract holds ambient) clear (root top groups) before
      (fun state result => Available state result ∧ result.free = [] ∧
        ∀ edge ∈ edges, ∀ term, EdgeMeaning (meaning holds ambient) holds edge term → meaning holds ambient result term) := by
  have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  apply bind_certified (Contract holds ambient) clear _ _ before
    (fun state rows => All₂ (fun inputs results => RowsPost holds ambient inputs state results) groups rows) _
    (paired_map_certified holds ambient clear (group top) (fun state edges => Edges state edges ∧ ClosedEdges edges)
      (fun state inputs results => RowsPost holds ambient inputs state results)
      (fun _ _ effect _ ready => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (ready.1 edge member)), ready.2⟩)
      (fun _ _ effect _ _ post => post.grows ⟨effect.keeps, effect.semantic⟩) groups
      (fun edges member state semantic costs ready => group_certified clear top holds ambient clearTrue topTrue edges
        (grouping.keys _ _ edges member) state semantic costs ready.1 ready.2)
      before semantic costs (fun group member => ⟨(fun edge included => resident edge (original group member edge included)),
        fun edge included => closed edge (original group member edge included)⟩))
  intro rows middle effect ready
  have rowResident : ∀ own ∈ rows, Edges middle own := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.resident))
  have rowClosed : ∀ own ∈ rows, ClosedEdges own := EnumerationSoundness.all₂_outputs _ _ _ (ready.imp (fun _ _ post => post.closed))
  have flatResident : Edges middle rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowResident own member edge included
  have flatClosed : ClosedEdges rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowClosed own member edge included
  have checked := SourceCurrentMemoMergeEffects.node_certified clear rows.flatten middle effect.semantic effect.costs flatResident flatClosed
  refine ⟨checked.1, checked.2.1, checked.2.2, ?_⟩
  intro edge member term accepted
  obtain ⟨group, member, included⟩ := List.mem_flatten.mp (grouping.partition.mem_iff.mpr member)
  obtain ⟨own, present, post⟩ := SymbolicSmartRows.all₂_child _ _ _ ready group member
  obtain ⟨selected, included, run⟩ := post.covers edge included term accepted
  exact (MergedColdInterpretation.makeNode_exact middle effect.semantic.ready.semantic.1.normal.facts
    (meaning holds ambient) rows.flatten flatResident holds (InternedGuardedLanguage.laws holds ambient) term).mpr
    ⟨selected, List.mem_flatten.mpr ⟨own, present, included⟩, run⟩

/-- Every actual source body derives physical and independent language obligations for its requests. -/
theorem body_certified (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    Certified (Contract holds ambient) clear (body top input) before (fun after output => Contract holds ambient input before output after) := by
  cases input with
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
        have rowsClosed : ClosedEdges edges := fun edge member child inner =>
          MergedOrdinaryHeight.closed_child before facts.coherent entry edges depth free available.resident closed edge member child inner
        have checked := root_certified clear top holds ambient clearTrue topTrue edges (MergedSourceGrouping.groups edges)
          (MergedSourceGrouping.groups_correct edges) before semantic costs resident rowsClosed
        exact checked.mono (by
          intro state result ready
          refine ⟨⟨ready.1, fun _ => ready.2.1⟩, ?_⟩
          intro term accepted
          obtain ⟨edge, member, run⟩ := ((InternedGuardedLanguage.laws holds ambient).node entry edges depth [] term).mp accepted
          exact ready.2.2 edge member term run)
      · simp only [body, closed, ite_false, Certified]
        exact ⟨⟨available, id⟩, fun _ accepted => accepted⟩
  | empty | reference | mu | union => exact ⟨⟨available, id⟩, fun _ accepted => accepted⟩

end MicroCFTA.SourceCurrentMemoMergeLanguage
