import MicroCFTA.SourceCurrentMemoMergeEffects

/-!
# Direct request bounds inside actual memo-aware merge bodies

A direct receipt follows instruction order. It retains the actual request
heap and result table. A request records its completed Call but does not
include the requests inside that Call's body. Local certificates check the
request input height before they use the returned physical contract.
-/
namespace MicroCFTA.SourceCurrentMemoMergeRequestBounds
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects
open MergedOrdinaryHeight
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- One direct request retains its exact argument, result, heap, and table states. -/
structure Occurrence (Symbol Guard : Type) where
  input : Value Symbol Guard
  before : State Symbol Guard
  memo : Memo Symbol Guard
  output : Value Symbol Guard
  after : State Symbol Guard
  saved : Memo Symbol Guard

/-- Direct requests retain source sequencing and leave nested bodies opaque. -/
inductive Direct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
    {Output : Type} → Code Symbol Guard Output → State Symbol Guard → Memo Symbol Guard →
      Output → State Symbol Guard → Memo Symbol Guard → List (Occurrence Symbol Guard) → Prop where
  | pure (value : Output) (state : State Symbol Guard) (memo : Memo Symbol Guard) :
      Direct clear top (.pure value) state memo value state memo []
  | work (job : Work Symbol Guard Output) (state : State Symbol Guard) (memo : Memo Symbol Guard) :
      Direct clear top (.work job) state memo (run job state).1 (run job state).2 memo []
  | select (fuel : Nat) (done : SourceMergedSelection.select clear fuel inputs before = .done values after) :
      Direct clear top (.select inputs) before memo values after memo []
  | request (actual : Call clear top input before memo output after saved) :
      Direct clear top (.request input) before memo output after saved [⟨input, before, memo, output, after, saved⟩]
  | bind (first : Direct clear top code before memo value middle current earlier)
      (later : Direct clear top (next value) middle current output after saved following) :
      Direct clear top (.bind code next) before memo output after saved (earlier ++ following)

variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual completed instruction has an ordered direct-request receipt. -/
theorem direct_exists {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∃ events, Direct clear top code before memo output after saved events := by
  induction actual using Run.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | pure => exact ⟨[], .pure _ _ _⟩
  | work => exact ⟨[], .work _ _ _⟩
  | select fuel done => exact ⟨[], .select fuel done⟩
  | request actual _ => exact ⟨_, .request actual⟩
  | bind _ _ first later =>
      obtain ⟨earlier, first⟩ := first
      obtain ⟨following, later⟩ := later
      exact ⟨_, .bind first later⟩
  | hit | miss => trivial

/-- A direct receipt erases to the exact completed instruction execution. -/
theorem Direct.graph {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output} {events : List (Occurrence Symbol Guard)}
    (actual : Direct clear top code before memo output after saved events) : Run clear top code before memo output after saved := by
  induction actual with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | select fuel done => exact .select fuel done
  | request actual => exact .request actual
  | bind _ _ first later => exact .bind first later

/-- Every retained occurrence contains an actual completed Call at its recorded heap and table. -/
theorem Direct.calls {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output} {events : List (Occurrence Symbol Guard)}
    (actual : Direct clear top code before memo output after saved events) :
    ∀ event ∈ events, Call clear top event.input event.before event.memo event.output event.after event.saved := by
  induction actual with
  | pure | work | select => simp
  | request actual => intro event member; cases List.mem_singleton.mp member; exact actual
  | bind _ _ first later =>
      intro event member
      rcases List.mem_append.mp member with member | member
      · exact first event member
      · exact later event member

/-- Local instruction certificates check the request bound before the returned physical contract. -/
def Bounded (limit : Nat) (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop) : Prop :=
  match code with
  | .pure value => post before value
  | .work job => Effect before (run job before).2 ∧ post (run job before).2 (run job before).1
  | .select inputs => Values before inputs ∧ ClosedValues inputs ∧ ∀ fuel values after,
      SourceMergedSelection.select clear fuel inputs before = .done values after → Effect before after → post after values
  | .request input => Available before input ∧ height input < limit ∧ ∀ output after,
      Effect before after → Contract input before output after → post after output
  | .bind first next => ∃ intermediate : State Symbol Guard → _ → Prop,
      Bounded limit clear first before intermediate ∧ ∀ value middle,
        Effect before middle → intermediate middle value → Bounded limit clear (next value) middle post

private theorem bind_bounded (limit : Nat) (clear : Guard → Bool)
    (first : Code Symbol Guard First) (next : First → Code Symbol Guard Output) (before : State Symbol Guard)
    (pre : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (checked : Bounded limit clear first before pre)
    (later : ∀ value middle, Effect before middle → pre middle value → Bounded limit clear (next value) middle post) :
    Bounded limit clear (.bind first next) before post := ⟨pre, checked, later⟩

/-- A retained request has a strictly smaller input and derived physical validity at its reached heap. -/
def Reached (limit : Nat) (before : State Symbol Guard) (event : Occurrence Symbol Guard) : Prop :=
  height event.input < limit ∧ Effect before event.before ∧ Stored event.before event.memo ∧ Available event.before event.input

/-- Actual instruction induction derives every local request bound and its causal heap prefix. -/
theorem Direct.bounded {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output} {events : List (Occurrence Symbol Guard)}
    (actual : Direct clear top code before memo output after saved events) :
    ∀ (limit : Nat) (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Stored before memo →
      Bounded limit clear code before post →
      Effect before after ∧ Stored after saved ∧ post after output ∧ ∀ event ∈ events, Reached limit before event := by
  induction actual with
  | pure value state memo =>
      intro limit post semantic costs stored checked
      exact ⟨effect_refl _ semantic costs, stored, checked, by simp⟩
  | work job state memo =>
      intro limit post semantic costs stored checked
      exact ⟨checked.1, stored.grows checked.1.keeps, checked.2, by simp⟩
  | select fuel done =>
      intro limit post semantic costs stored checked
      have effects := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _ semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨effects.keeps, effects.semantic, effects.costs⟩
      exact ⟨effect, stored.grows effect.keeps, checked.2.2 fuel _ _ done effect, by simp⟩
  | request actual =>
      intro limit post semantic costs stored checked
      have effects := call_effects actual semantic costs stored checked.1
      refine ⟨effects.1, effects.2.1, checked.2.2 _ _ effects.1 effects.2.2, ?_⟩
      intro event member
      cases List.mem_singleton.mp member
      exact ⟨checked.2.1, effect_refl _ semantic costs, stored, checked.1⟩
  | bind first later ihFirst ihLater =>
      intro limit post semantic costs stored checked
      obtain ⟨pre, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstStored, ready, earlier⟩ := ihFirst limit pre semantic costs stored firstChecked
      obtain ⟨laterEffect, laterStored, returned, following⟩ := ihLater limit post firstEffect.semantic firstEffect.costs firstStored
        (nextChecked _ _ firstEffect ready)
      refine ⟨firstEffect.trans laterEffect, laterStored, returned, ?_⟩
      intro event member
      rcases List.mem_append.mp member with member | member
      · exact earlier event member
      · have reached := following event member
        exact ⟨reached.1, firstEffect.trans reached.2.1, reached.2.2⟩

private theorem Bounded.mono {limit : Nat} {clear : Guard → Bool} {code : Code Symbol Guard Output}
    {before : State Symbol Guard} {post nextPost : State Symbol Guard → Output → Prop}
    (checked : Bounded limit clear code before post)
    (implies : ∀ after output, post after output → nextPost after output) : Bounded limit clear code before nextPost := by
  induction code generalizing before with
  | pure value => exact implies _ _ checked
  | work job => exact ⟨checked.1, implies _ _ checked.2⟩
  | select inputs => exact ⟨checked.1, checked.2.1, fun fuel values after done effect => implies _ _ (checked.2.2 fuel values after done effect)⟩
  | request input => exact ⟨checked.1, checked.2.1, fun output after effect returned => implies _ _ (checked.2.2 output after effect returned)⟩
  | bind first next ihFirst ihNext =>
      obtain ⟨pre, firstChecked, later⟩ := checked
      exact ⟨pre, firstChecked, fun value middle effect valid => ihNext value (later value middle effect valid) implies⟩

private theorem map_bounded (limit : Nat) (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ value, post before value → post after value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Bounded limit clear (call request) before post)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Bounded limit clear (map call requests) before (fun after values => ∀ value ∈ values, post after value) := by
  induction requests generalizing before with
  | nil => exact by simp [map, Bounded]
  | cons first rest ih =>
      apply bind_bounded limit clear _ _ before post _
        (checked first List.mem_cons_self before semantic costs (inputs first List.mem_cons_self))
      intro value middle effect valid
      apply bind_bounded limit clear _ _ middle _ _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact postGrows middle after later _ valid
      · exact ready output member

private theorem request_bounded (limit : Nat) (clear : Guard → Bool) (value : Value Symbol Guard)
    (before : State Symbol Guard) (ready : ValueReady before value) (bound : height value < limit) :
    Bounded limit clear (.request value) before ValueReady :=
  ⟨ready.1, bound, fun _ _ _ returned => ⟨returned.1, returned.2 ready.2⟩⟩

private theorem retained_bounded (limit : Nat) (positive : 0 < limit) (clear : Guard → Bool)
    (inputs : List (Value Symbol Guard)) (bounded : ∀ value ∈ inputs, height value < limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before inputs) (closed : ClosedValues inputs) :
    Bounded limit clear (retainedColumn inputs) before ValueReady := by
  have branches (values : List (Value Symbol Guard)) (bounded : ∀ value ∈ values, height value < limit)
      (available : Values before values) (closed : ClosedValues values) :
      Bounded limit clear
        (if values.any recursiveBoundary then .work (makeUnion values)
          else .bind (.work (ordinaryUnion values)) Code.request) before ValueReady := by
    by_cases boundary : values.any recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeUnion_noNewMu values before)⟩, checked.2⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      have heightBound := ordinaryUnion_bound values before semantic.ready.semantic.1.normal.facts.coherent
        semantic.ready.semantic.1.normal.facts.linked (fun value member => (available value member).resident) (limit - 1)
        (fun value member => by have less := bounded value member; omega)
      apply bind_bounded limit clear (.work (ordinaryUnion values)) Code.request before
        (fun state result => ValueReady state result ∧ height result < limit) _
        ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
          (InternedShallowHeap.makeNode_noNewMu _ before)⟩, ⟨checked.2.1, checked.2.2.1⟩, by omega⟩
      exact fun value middle _ ready => request_bounded limit clear value middle ready.1 ready.2
  cases inputs with
  | nil => exact branches [] bounded available closed
  | cons first rest =>
      cases rest with
      | nil => exact ⟨available first List.mem_cons_self, closed first List.mem_cons_self⟩
      | cons second rest => exact branches (first :: second :: rest) bounded available closed

private theorem column_bounded (limit : Nat) (positive : 0 < limit) (clear : Guard → Bool)
    (inputs : List (Value Symbol Guard)) (bounded : ∀ value ∈ inputs, height value < limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (_costs : CostHeap before)
    (available : Values before inputs) (closed : ClosedValues inputs) :
    Bounded limit clear (column inputs) before ValueReady := by
  apply bind_bounded limit clear _ _ before
    (fun heap values => Values heap values ∧ ClosedValues values ∧ ∀ value ∈ values, height value < limit) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done _
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    exact ⟨checked.2.1, checked.2.2.1, fun value member => bounded value (checked.2.2.2.1 value member)⟩
  · intro values middle effect ready
    exact retained_bounded limit positive clear values ready.2.2 middle effect.semantic effect.costs ready.1 ready.2.1

private theorem small_bounded (limit : Nat) (clear : Guard → Bool)
    (edge : EdgeValue Symbol Guard) (bounded : ∀ value ∈ edge.children, height value < limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) (ready : EdgeReady before edge) :
    Bounded limit clear (small edge) before EdgeReady := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge ready.1
  apply bind_bounded limit clear _ _ before (fun heap values => ∀ value ∈ values, ValueReady heap value) _
    (map_bounded limit clear Code.request ValueReady ValueReady
      (fun _ _ effect value ready => value_grows effect value ready)
      (fun _ _ effect value ready => value_grows effect value ready) edge.children
      (fun value member heap _ _ ready => request_bounded limit clear value heap ready (bounded value member)) before semantic costs
      (fun value member => ⟨available value member, ready.2 value member⟩))
  intro values middle effect valid
  exact SourceCurrentMemoMergeEffects.edge_certified clear edge.entry.key.symbol edge.entry.key.constraint values middle effect.semantic effect.costs
    (fun value member => (valid value member).1) (fun value member => (valid value member).2)

private theorem large_bounded (limit : Nat) (positive : 0 < limit) (clear : Guard → Bool) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (bounded : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, height value < limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest)) :
    Bounded limit clear (large top first rest) before EdgeReady := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply bind_bounded limit clear _ _ before (fun heap values => ∀ value ∈ values, ValueReady heap value) _
    (map_bounded limit clear column (fun heap values => Values heap values ∧ ClosedValues values) ValueReady
      (fun _ _ effect _ ready => ⟨(fun value member => effect.keeps.available _ (ready.1 value member)), ready.2⟩)
      (fun _ _ effect value ready => value_grows effect value ready) columns
      (fun values member heap semantic costs ready => column_bounded limit positive clear values (by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original values member value included
        exact bounded edge outer value inner) heap semantic costs ready.1 ready.2)
      before semantic costs (fun column member => ⟨(by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact closed edge outer value inner)⟩))
  intro values middle effect valid
  exact SourceCurrentMemoMergeEffects.edge_certified clear first.entry.key.symbol top values middle effect.semantic effect.costs
    (fun value member => (valid value member).1) (fun value member => (valid value member).2)

private theorem group_bounded (limit : Nat) (positive : 0 < limit) (clear : Guard → Bool) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (bounded : ∀ edge ∈ edges, ∀ value ∈ edge.children, height value < limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    Bounded limit clear (group top edges) before (fun heap rows => ∀ edge ∈ rows, EdgeReady heap edge) := by
  unfold group
  split
  · exact map_bounded limit clear small EdgeReady EdgeReady
      (fun _ _ effect edge ready => edge_grows effect edge ready) (fun _ _ effect edge ready => edge_grows effect edge ready)
      edges (fun edge member heap semantic costs ready => small_bounded limit clear edge (bounded edge member) heap semantic costs ready)
      before semantic costs (fun edge member => ⟨resident edge member, closed edge member⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply bind_bounded limit clear _ _ before EdgeReady _
          (large_bounded limit positive clear top first rest bounded before semantic costs resident closed)
        intro edge middle _ ready
        intro value member
        have same := List.mem_singleton.mp member
        exact same ▸ ready

private theorem root_bounded (limit : Nat) (positive : 0 < limit) (clear : Guard → Bool) (top : Guard)
    (groups : List (List (EdgeValue Symbol Guard)))
    (bounded : ∀ group ∈ groups, ∀ edge ∈ group, ∀ value ∈ edge.children, height value < limit)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (closed : ∀ group ∈ groups, ClosedEdges group) :
    Bounded limit clear (root top groups) before ValueReady := by
  apply bind_bounded limit clear _ _ before (fun heap rows => ∀ row ∈ rows, ∀ edge ∈ row, EdgeReady heap edge) _
    (map_bounded limit clear (group top) (fun heap edges => Edges heap edges ∧ ClosedEdges edges)
      (fun heap rows => ∀ edge ∈ rows, EdgeReady heap edge)
      (fun _ _ effect _ ready => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (ready.1 edge member)), ready.2⟩)
      (fun _ _ effect _ ready edge member => edge_grows effect edge (ready edge member)) groups
      (fun edges member heap semantic costs ready => group_bounded limit positive clear top edges (bounded edges member)
        heap semantic costs ready.1 ready.2)
      before semantic costs (fun edges member => ⟨resident edges member, closed edges member⟩))
  intro rows middle effect valid
  apply SourceCurrentMemoMergeEffects.node_certified clear rows.flatten middle effect.semantic effect.costs
  · intro edge member
    obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member
    exact (valid row outer edge inner).1
  · intro edge member
    obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member
    exact (valid row outer edge inner).2

/-- The literal source body derives its own strict request bound from the original input. -/
theorem body_bounded (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    Bounded (height input) clear (body top input) before (fun after output => Contract input before output after) := by
  cases input with
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
        have rowsClosed : ClosedEdges edges := fun edge member child inner =>
          closed_child before facts.coherent entry edges depth free available.resident closed edge member child inner
        have grouping := MergedSourceGrouping.groups_correct edges
        have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ MergedSourceGrouping.groups edges)
            (edge : EdgeValue Symbol Guard) (inner : edge ∈ group) : edge ∈ edges :=
          grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, inner⟩)
        have checked := root_bounded (height (.node entry edges depth [])) (by simp only [height]; omega) clear top
          (MergedSourceGrouping.groups edges)
          (fun group member edge inner value included => child_lt entry edges depth [] edge (original group member edge inner) value included)
          before semantic costs
          (fun group member edge inner => resident edge (original group member edge inner))
          (fun group member edge inner => rowsClosed edge (original group member edge inner))
        exact checked.mono (fun _ _ ready => ⟨ready.1, fun _ => ready.2⟩)
      · simp only [body, closed, ite_false, Bounded]
        exact ⟨available, id⟩
  | empty | reference | mu | union => exact ⟨available, id⟩

/-- Every direct request in an actual body has a smaller input at its exact reached physical state. -/
theorem body_requests {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (body top input) before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    ∃ events, Direct clear top (body top input) before memo output after saved events ∧
      ∀ event ∈ events, Reached (height input) before event := by
  obtain ⟨events, receipt⟩ := direct_exists actual
  have checked := receipt.bounded (height input) _ semantic costs stored (body_bounded clear top input before semantic costs available)
  exact ⟨events, receipt, checked.2.2.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- A direct request cannot use the physical key of a retained ancestor with no smaller height. -/
theorem Reached.not_ancestor {limit : Nat} {before : State Symbol Guard} {event : Occurrence Symbol Guard}
    (reached : Reached limit before event) (ancestor : Value Symbol Guard)
    (available : Available before ancestor) (above : limit ≤ height ancestor) :
    event.input.referenceOf ≠ ancestor.referenceOf := by
  intro equal
  have resident := reached.2.1.keeps.available ancestor available
  have same := InternedFreshProbeKeys.resident_reference_injective event.before
    reached.2.1.semantic.ready.semantic.1.normal.facts.coherent event.input ancestor reached.2.2.2.resident resident.resident equal
  have less := reached.1
  rw [same] at less
  omega

end MicroCFTA.SourceCurrentMemoMergeRequestBounds
