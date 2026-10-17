import MicroCFTA.SourceEqualityAnnotationProjection
import MicroCFTA.SourceCurrentAllocatedSeededQuery

/-!
# Physical guard carriers through supported open seeded projection

An open supported head has a finite chain of same-heap unfolds.
A closed tail retains the physical annotation heap through its actual read.
Selected projection retains this predicate through its ordered child calls.
Unrelated ordinary children and forest roots can remain open.
-/
namespace MicroCFTA.SourceCurrentSeededProjectionCarrier
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedFreshOrdinaryExposure
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredHead
open SourceEqualityProjectionGraph
open SourceCurrentSecondaryProjectionSupport (Support)
open SourceCurrentSecondaryProjectionComplete (ForestSupport)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceSecondaryGateHead (WarmHead)
open SourceEqualityAnnotationHeap (Heap)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem select_natural (values : List A) (index : Nat) : select values (Int.ofNat index) = values[index]? := by
  simp only [select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl

private theorem unfolded_available {value next : Value Symbol Guard} {state : State Symbol Guard}
    (semantic : SemanticReady state) (available : Available state value)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold value state = .done next state) : Available state next := by
  obtain ⟨result, after, done, _, _, resultAvailable, _⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete value state semantic available
  obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
  cases sameValue
  cases sameState
  exact resultAvailable

private theorem warm_collect (annotation : Guard → Prop) {state : State Symbol Guard} {value : Value Symbol Guard}
    (support : WarmHead state value) (semantic : SemanticReady state) (available : Available state value)
    (seen : List Nat) (heap : Heap annotation state) :
    ∃ fuel edges after, collect fuel state seen [value] = .done edges after ∧ Heap annotation after := by
  revert seen available semantic
  induction support with
  | empty => intro _ _ seen; exact ⟨1, [], _, rfl, heap⟩
  | ordinary =>
      intro _ _ seen
      exact ⟨1, _, _, by simp only [collect, MergedSourceExposure.Result.prepend, List.append_nil,
        InternedEdgeResidency.nodeEdges], heap⟩
  | closed closed =>
      intro semantic available seen
      obtain ⟨fuel, edges, after, done, _⟩ :=
        SourceSecondaryGateHead.collect_complete (.closed closed) semantic available seen
      refine ⟨fuel, edges, after, done, ?_⟩
      simpa only [done, MergedSourceExposure.Result.state] using
        SourceEqualityAnnotationExposure.collect_heap annotation fuel state semantic.ready.semantic
          semantic.ready.covered heap seen [value]
          (by intro other member; simpa only [List.mem_singleton.mp member] using available)
          (by intro other member; simpa only [List.mem_singleton.mp member] using closed)
  | @unfold entry body depth ordinary next actual rest ih =>
      intro semantic available seen
      by_cases visited : entry.identity ∈ seen
      · exact ⟨1, [], _, by simp only [collect, ite_eq_left visited], heap⟩
      · obtain ⟨fuel, edges, after, done, finalHeap⟩ :=
          ih semantic (unfolded_available semantic available actual) (entry.identity :: seen)
        exact ⟨fuel + 1, edges, after, by simpa only [collect, ite_eq_right visited, actual] using done, finalHeap⟩

private theorem warm_read (annotation : Guard → Prop) {state : State Symbol Guard} {value : Value Symbol Guard}
    (support : WarmHead state value) (semantic : SemanticReady state) (available : Available state value)
    (heap : Heap annotation state) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧ Heap annotation after := by
  cases support with
  | empty => exact ⟨0, [], _, rfl, heap⟩
  | ordinary => exact ⟨0, _, _, rfl, heap⟩
  | closed closed =>
      obtain ⟨edges, after, read, _⟩ := SourceEqualityProjectionRead.complete _ _ semantic available closed
      have retained := SourceEqualityAnnotationProjection.read annotation read semantic available closed heap
      cases read with
      | done fuel completed => exact ⟨fuel, edges, after, completed, retained⟩
  | @unfold entry body depth ordinary next actual rest =>
      obtain ⟨fuel, edges, after, done, retained⟩ :=
        warm_collect annotation (.unfold actual rest) semantic available [] heap
      have fallback : (collect fuel state [] [.mu entry body depth ordinary]).canonical =
          .done (canonicalEdges edges) after := by rw [done]; rfl
      cases next with
      | node entry edges depth free => exact ⟨0, edges, state, by simp only [nodeEdges, actual], heap⟩
      | empty | reference | union | mu =>
          exact ⟨fuel, canonicalEdges edges, after, by simpa only [nodeEdges, actual] using fallback, retained⟩

/-- A supported warm head retains the physical guard predicate at the exact actual return. -/
theorem head (annotation : Guard → Prop) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Head value before result after) (semantic : SemanticReady before)
    (available : Available before value) (warm : WarmHead before value) (heap : Heap annotation before) :
    Heap annotation after := by
  obtain ⟨fuel, edges, middle, exposed, retained⟩ := warm_read annotation warm semantic available heap
  have own : Head value before (run (makeNode edges) middle).1 (run (makeNode edges) middle).2 :=
    .read fuel edges middle exposed rfl
  have finalHeap := SourceEqualityAnnotationHeap.run annotation _
    (SourceEqualityAnnotationHeap.makeNode annotation edges) middle retained
  obtain ⟨_, sameState⟩ := own.unique actual
  exact sameState ▸ finalHeap

private theorem rows_carrier (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor) (path : EqualityNormalize.Path) (index : Nat)
    (child : ∀ {value result : Value Symbol Guard} {before after : State Symbol Guard},
      Project (path.map Int.ofNat) value before result after → SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value → Heap annotation before → Heap annotation after)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} {values : List (Value Symbol Guard)}
    (actual : ProjectRows (path.map Int.ofNat) (Int.ofNat index) edges before values after)
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (supported : ∀ edge ∈ edges, ∀ value, edge.children[index]? = some value → Support unconstrained anchor path value)
    (heap : Heap annotation before) : Heap annotation after := by
  induction edges generalizing before after values with
  | nil => cases actual; exact heap
  | cons edge edges ih =>
      cases actual with
      | missing absent rest =>
          exact ih rest semantic (fun row member => resident row (List.mem_cons_of_mem _ member)) growth
            (fun row member => supported row (List.mem_cons_of_mem _ member)) heap
      | selected found first rest =>
          have selected : edge.children[index]? = some _ := by simpa only [select_natural] using found
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) _ (select_member found)
          have support := supported edge List.mem_cons_self _ selected
          have middleHeap := child first semantic available growth support heap
          have physical := SourceCurrentSecondaryProjectionComplete.node_verified unconstrained anchor anchorSemantic anchorReady
            first semantic available growth support
          exact ih rest physical.2.1
            (fun row member => InternedEdgeResidency.edge_grows before _ physical.1.growth row
              (resident row (List.mem_cons_of_mem _ member)))
            (grows_trans growth physical.1.growth)
            (fun row member => supported row (List.mem_cons_of_mem _ member)) middleHeap

private theorem ordinary_carrier (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor) (path : EqualityNormalize.Path) (index : Nat)
    (child : ∀ {value result : Value Symbol Guard} {before after : State Symbol Guard},
      Project (path.map Int.ofNat) value before result after → SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value → Heap annotation before → Heap annotation after)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project ((index :: path).map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (ordinary : Ordinary value)
    (supported : ∀ edge ∈ InternedEdgeResidency.nodeEdges value, ∀ child,
      edge.children[index]? = some child → Support unconstrained anchor path child)
    (heap : Heap annotation before) : Heap annotation after := by
  cases actual with
  | empty => exact heap
  | ordinary rows joined =>
      have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
      have middleHeap := rows_carrier annotation unconstrained anchor anchorSemantic anchorReady path index child
        rows semantic resident growth supported heap
      have physical := SourceCurrentSecondaryProjectionComplete.rows_verified unconstrained anchor anchorSemantic anchorReady
        rows semantic resident growth supported
      exact SourceEqualityAnnotationProjection.union annotation joined physical.2.1 physical.2.2.1 physical.2.2.2 middleHeap
  | recursive recursive _ _ => cases value <;> cases recursive <;> cases ordinary

/-- Each actual node projection retains the carrier under its original anchored selected support. -/
theorem node (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor) (path : EqualityNormalize.Path)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project (path.map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (supported : Support unconstrained anchor path value) (heap : Heap annotation before) : Heap annotation after := by
  induction path generalizing value result before after with
  | nil => cases actual; exact heap
  | cons index path ih =>
      rcases supported with closed | ⟨anchorAvailable, gate⟩
      · exact SourceEqualityAnnotationProjection.node annotation actual semantic available closed heap
      · cases value with
        | empty => cases actual; exact heap
        | reference | union => cases gate
        | node entry edges depth free =>
            exact ordinary_carrier annotation unconstrained anchor anchorSemantic anchorReady path index ih
              actual semantic available growth True.intro
              (fun edge member child found => SourceCurrentSecondaryProjectionSupport.ordinary_selected_support
                (Or.inr ⟨anchorAvailable, gate⟩) anchorSemantic semantic available edge member child found) heap
        | mu entry body depth ordinary =>
            cases actual with
            | recursive recursive exposedHead body =>
                have physical := SourceCurrentSecondaryProjectionSupport.head_verified gate anchorSemantic anchorAvailable
                  semantic available growth exposedHead
                have warm := SourceCurrentSecondaryProjectionSupport.support_warm_head
                  (Or.inr ⟨anchorAvailable, gate⟩) anchorSemantic before growth
                have middleHeap := head annotation exposedHead semantic available warm heap
                exact ordinary_carrier annotation unconstrained anchor anchorSemantic anchorReady path index ih body
                  physical.2.1 physical.2.2.1 (grows_trans growth physical.1.growth) physical.2.2.2
                  (SourceCurrentSecondaryProjectionSupport.head_selected_support gate anchorSemantic anchorAvailable
                    semantic available growth exposedHead) middleHeap

/-- Ordered row projection retains the same carrier through every selected child and returned heap. -/
theorem rows (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor) (path : EqualityNormalize.Path) (index : Nat)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} {values : List (Value Symbol Guard)}
    (actual : ProjectRows (path.map Int.ofNat) (Int.ofNat index) edges before values after)
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (supported : ∀ edge ∈ edges, ∀ value, edge.children[index]? = some value → Support unconstrained anchor path value)
    (heap : Heap annotation before) : Heap annotation after :=
  rows_carrier annotation unconstrained anchor anchorSemantic anchorReady path index
    (node annotation unconstrained anchor anchorSemantic anchorReady path) actual semantic resident growth supported heap

/-- Forest projection preserves the original carrier without closure of unrelated roots. -/
theorem forest (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
    (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor) (path : EqualityNormalize.Path)
    {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest (path.map Int.ofNat) values before result after)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (supported : ForestSupport unconstrained anchor path values) (heap : Heap annotation before) : Heap annotation after := by
  cases path with
  | nil => cases actual with
    | root joined => exact SourceEqualityAnnotationProjection.union annotation joined semantic available supported heap
  | cons index path =>
      cases actual with
      | missing absent => exact heap
      | selected found body =>
          exact node annotation unconstrained anchor anchorSemantic anchorReady path body semantic
            (available _ (select_member found)) growth
            (supported _ (by simpa only [select_natural] using found)) heap

local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The literal checked operand keeps the same physical carrier at its exact full-state return. -/
theorem operand (annotation : SourceGuard → Prop) (unconstrained : Value SourceSymbol SourceGuard → Bool)
    (anchor : State SourceSymbol SourceGuard) (anchorSemantic : SemanticReady anchor)
    (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {path : List Int} {values : List (Value SourceSymbol SourceGuard)} {result : Value SourceSymbol SourceGuard}
    {before after : SourceEqualityNativeDemand.State width}
    (actual : SourceCurrentAllocatedSeededQuery.Operand path values before result after)
    (semantic : SemanticReady before.native.machine.heap) (available : Values before.native.machine.heap values)
    (growth : Grows anchor before.native.machine.heap) (supported : PathSupport unconstrained anchor path values)
    (heap : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  obtain ⟨natural, rfl, supported⟩ := supported
  cases actual with
  | force result final projected =>
      exact forest annotation unconstrained anchor anchorSemantic anchorReady natural projected semantic available growth supported heap

end MicroCFTA.SourceCurrentSeededProjectionCarrier
