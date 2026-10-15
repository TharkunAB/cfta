import MicroCFTA.SourceMergedAnnotationWorker
import MicroCFTA.SourceEqualityNativeMerge
import MicroCFTA.SourceCurrentOpenExposureFields

/-!
# Stored heap invariants through actual merging

Actual bounded comparison reads retain stored unfolding costs and physical
edge annotations. Available open operands are permitted. Merge recursion
follows the source closed-ordinary test and actual constructor requests.
CostHeap records unfolding probe readback. It does not bound execution cost.
These results do not model global merge memo publication or runtime forcing.
-/
namespace MicroCFTA.SourceCurrentMergedHeapEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonEffects (bind_done)
open SourceEqualityAnnotationHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A successful stage retains actual cache effects and preserves physical edge annotations. -/
structure Effect (annotation : Guard → Prop) (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  annotations : Heap annotation before → Heap annotation after

/-- Annotation effects retain the previously proved source cache effects. -/
theorem Effect.original {annotation : Guard → Prop} {before after : State Symbol Guard} (effect : Effect annotation before after) :
    SourceMergedComparisonEffects.Effect before after := ⟨effect.keeps, effect.semantic⟩

/-- A direct Boolean return has no cache effects. -/
theorem pure_effect (annotation : Guard → Prop) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) (answer result : Bool)
    (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) : Effect annotation before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩

/-- Ordered successful effects compose semantic caches, histories, and annotation preservation. -/
theorem Effect.trans {annotation : Guard → Prop} {before middle after : State Symbol Guard} (first : Effect annotation before middle) (second : Effect annotation middle after) : Effect annotation before after :=
  ⟨first.keeps.trans second.keeps, second.semantic, second.costs, fun heap => second.annotations (first.annotations heap)⟩

/-- A completed actual row read retains both heaps and returns resident rows. -/
theorem read_effect (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after) :
    Effect annotation before after ∧ Edges after rows := by
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done edges final =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      have kept : Keeps before after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.keeps
      have ready : SemanticReady after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.semantic
      have retained : CostHeap after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.costs
      refine ⟨⟨kept, ready, retained, ?_⟩, checked.rows rows after actual⟩
      intro heap
      simpa only [actual, MergedSourceExposure.Result.state] using
        SourceCurrentOpenExposureFields.nodeEdges_heap annotation fuel value before semantic heap available
  | pending | unresolved | exhausted =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      cases done

/-- Callback effects use only actual available operands and their current heaps. -/
def Callback (annotation : Guard → Prop) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → CostHeap before → Available before wide → Available before narrow →
    ∀ answer after, compare wide narrow before = .done answer after → Effect annotation before after

/-- The source zip conjunction preserves annotations even when a list ends early. -/
theorem children_effect (annotation : Guard → Prop) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback annotation compare) (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) : Effect annotation before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_effect annotation before semantic costs true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_effect annotation before semantic costs true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have effect := callback wide narrow before semantic costs (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => exact effect.trans (pure_effect annotation middle effect.semantic effect.costs false answer after later)
          | true => exact effect.trans (ih narrows middle effect.semantic effect.costs
              (fun value member => effect.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.keeps.available value (narrowInputs value (List.mem_cons_of_mem _ member))) later)

/-- Actual ordered edge-cover search retains semantic cache fields and physical annotations. -/
theorem anyCover_effect (annotation : Guard → Prop) [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback annotation compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) : Effect annotation before after := by
  induction wides generalizing before with
  | nil => exact pure_effect annotation before semantic costs false answer after done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effect := children_effect annotation compare callback wide.children narrow.children before semantic costs
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs accepted middle first
        cases accepted with
        | true => exact effect.trans (pure_effect annotation middle effect.semantic effect.costs true answer after later)
        | false => exact effect.trans (ih middle effect.semantic effect.costs (fun value member => effect.keeps.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.keeps.growth edge (wideInputs edge (List.mem_cons_of_mem _ member))) later)
      · exact ih before semantic costs narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member)) done

/-- Each actual row read and cover search retains annotations and the next input scope. -/
theorem allRows_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback annotation compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) : Effect annotation before after := by
  induction narrows generalizing before with
  | nil => exact pure_effect annotation before semantic costs true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := read_effect annotation fuel wide before semantic costs wideInput wides readAfter read
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverFacts := anyCover_effect annotation clear compare callback narrow wides readAfter readFacts.1.semantic readFacts.1.costs
        (fun value member => readFacts.1.keeps.available value (childInputs value member)) readFacts.2 accepted middle covered
      have first : Effect annotation before middle := readFacts.1.trans coverFacts
      cases accepted with
      | false => exact first.trans (pure_effect annotation middle first.semantic first.costs false answer after rest)
      | true => exact first.trans (ih middle first.semantic first.costs (first.keeps.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.keeps.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member))) rest)

/-- Every completed structural comparison retains costs and annotations on available open or closed operands. -/
theorem check_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) : Effect annotation before after := by
  rw [check] at done
  split at done
  · exact pure_effect annotation before semantic costs true answer after done
  · split at done
    · exact pure_effect annotation before semantic costs false answer after done
    · split at done
      · exact pure_effect annotation before semantic costs true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_effect annotation before semantic costs true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := read_effect annotation (fuel + 1) narrow before semantic costs narrowInput narrows middle read
                      have rest := allRows_effect annotation (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                        (check_effect annotation clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.1.semantic readFacts.1.costs
                        (readFacts.1.keeps.available wide wideInput) readFacts.2 answer after later
                      exact readFacts.1.trans rest
termination_by fuel


open MergedPhysicalGroupColumns (closedMu)

/-- Every completed recursive-cover scan retains annotations and actual cache histories. -/
theorem anyAccepts_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (answer : Bool) (after : State Symbol Guard) (done : SourceMergedSelection.anyAccepts clear fuel narrow wides before = .done answer after) : Effect annotation before after := by
  induction wides generalizing before with
  | nil => exact pure_effect annotation before semantic costs false answer after done
  | cons wide wides ih =>
      by_cases narrowClosed : narrow.free = []
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_true] at done
        obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effects := check_effect annotation clear fuel [] wide narrow before semantic costs (wideInputs _ List.mem_cons_self) narrowInput accepted middle first
        cases accepted with
        | true => exact effects.trans (pure_effect annotation middle effects.semantic effects.costs true answer after later)
        | false => exact effects.trans (ih middle effects.semantic effects.costs (effects.keeps.available narrow narrowInput)
            (fun value member => effects.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member))) later)
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_false] at done
        exact pure_effect annotation before semantic costs false answer after done

/-- Successful actual filtering retains annotation heaps, semantic heaps, and both histories. -/
theorem retain_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (recInputs : Values before recursive) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.retain clear fuel recursive inputs before = .done retained after) : Effect annotation before after := by
  induction inputs generalizing before retained after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact ⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩
  | cons child inputs ih =>
      rw [SourceMergedSelection.retain] at done
      split at done
      · obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have parts := Result.done.inj returned
        cases parts.2
        exact ih before semantic costs recInputs (fun value member => available value (List.mem_cons_of_mem _ member)) rest after tail
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        have effects := anyAccepts_effect annotation clear fuel child recursive before semantic costs (available _ List.mem_cons_self) recInputs covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have parts := Result.done.inj returned
        cases parts.2
        exact effects.trans (ih middle effects.semantic effects.costs (fun value member => effects.keeps.available value (recInputs value member))
          (fun value member => effects.keeps.available value (available value (List.mem_cons_of_mem _ member))) rest after tail)

/-- The actual retention and identity filter preserve annotations at the returned cache. -/
theorem select_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done retained after) : Effect annotation before after := by
  obtain ⟨values, middle, filtered, returned⟩ := (bind_done _ _ retained after).mp done
  have checked := retain_effect annotation clear fuel (inputs.filter closedMu) inputs before semantic costs
    (fun value member => available value (List.mem_filter.mp member).1) available values middle filtered
  have parts := Result.done.inj returned
  cases parts.2
  exact checked

open InternedEdgeResidency (EdgeResident)
open MergedColdMerge (Action pure bind work map retainedColumn small)
open SourceMergedContracts

/-- Recursive stored cost preservation is required only at actual successful closed calls. -/
private def RecurseCost (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before, SemanticReady before → Available before value → value.free = [] →
    ∀ result after, call value before = .done result after → CostHeap before → CostHeap after

/-- Ordered maps retain stored costs through the actual effects of each earlier request. -/
private theorem map_cost (call : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop)
    (preGrows : ∀ before after, SourceMergedComparisonEffects.Effect before after → ∀ request, pre before request → pre after request)
    (requests : List Request)
    (effects : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request →
      ∀ result after, call request before = .done result after → SourceMergedComparisonEffects.Effect before after)
    (costLaw : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request →
      ∀ result after, call request before = .done result after → CostHeap before → CostHeap after)
    (before : State Symbol Guard) (semantic : SemanticReady before) (inputs : ∀ request ∈ requests, pre before request)
    (results : List Output) (after : State Symbol Guard) (done : map call requests before = .done results after)
    (heap : CostHeap before) : CostHeap after := by
  induction requests generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact heap
  | cons request requests ih =>
      obtain ⟨first, middle, called, later⟩ := (bind_done _ _ results after).mp done
      have checked := effects request List.mem_cons_self before semantic (inputs request List.mem_cons_self) first middle called
      have middleHeap := costLaw request List.mem_cons_self before semantic (inputs request List.mem_cons_self) first middle called heap
      obtain ⟨rest, final, mapped, returned⟩ := (bind_done _ _ results after).mp later
      have finalHeap := ih (fun request member => effects request (List.mem_cons_of_mem _ member))
        (fun request member => costLaw request (List.mem_cons_of_mem _ member)) middle checked.2
        (fun request member => preGrows before middle checked request (inputs request (List.mem_cons_of_mem _ member))) rest final mapped middleHeap
      have parts := Result.done.inj returned
      cases parts.2
      exact finalHeap

/-- Every retained-column branch preserves stored costs through literal union work and actual recursion. -/
private theorem retained_cost [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (costLaw : RecurseCost call)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) (heap : CostHeap before) : CostHeap after := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values)
      (done : (if values.any MergedOrdinaryHeight.recursiveBoundary then work (makeUnion values)
        else bind (work (MergedOrdinaryHeight.ordinaryUnion values)) call) before = .done result after) : CostHeap after := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true, work] at done
      have parts := Result.done.inj done
      cases parts.2
      exact InternedFreshOrdinaryCostHeap.preserve before _ heap (InternedShallowHeap.makeUnion_noNewMu values before)
    · simp only [boundary, Bool.false_eq_true, ite_false] at done
      obtain ⟨united, middle, constructed, called⟩ := (bind_done _ _ result after).mp done
      have parts := Result.done.inj constructed
      cases parts.1; cases parts.2
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      exact costLaw _ _ checked.1.2 checked.2.1 checked.2.2.1 result after called
        (InternedFreshOrdinaryCostHeap.preserve before _ heap (InternedShallowHeap.makeNode_noNewMu _ before))
  cases inputs with
  | nil => exact branches [] available closed done
  | cons first rest =>
      cases rest with
      | nil =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap
      | cons second rest => exact branches (first :: second :: rest) available closed done

/-- The actual repaired child filter and retained-column requests preserve stored costs in order. -/
private theorem column_cost [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (costLaw : RecurseCost call)
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before inputs) (closed : ClosedValues inputs)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.column call clear fuel inputs before = .done result after) (heap : CostHeap before) : CostHeap after := by
  obtain ⟨selected, middle, filtered, called⟩ := (bind_done _ _ result after).mp done
  have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
    (fun _ _ _ => rfl) inputs before semantic available closed selected middle filtered
  have filteredHeap := (select_effect (fun _ => True) clear fuel inputs before semantic heap available selected middle filtered).costs
  exact retained_cost call costLaw selected middle checked.1.2 checked.2.1 checked.2.2.1 result after called filteredHeap

/-- Small rows retain their actual original full guard after ordered recursive child effects. -/
private theorem small_cost [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (costLaw : RecurseCost call)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : EdgeResident before edge) (closed : ClosedValues edge.children) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) (heap : CostHeap before) : CostHeap after := by
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  have middleHeap := map_cost call (fun state value => Available state value ∧ value.free = [])
    (fun _ _ effect value valid => ⟨effect.1.available value valid.1, valid.2⟩) edge.children
    (fun value _ state ready valid result final actual => (law value state ready valid.1 valid.2 result final actual).1)
    (fun value _ state ready valid result final actual => costLaw value state ready valid.1 valid.2 result final actual)
    before semantic (fun value member => ⟨available value member, closed value member⟩) values middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact middleHeap

/-- Large groups retain stored costs through actual columns and the literal source Top guard. -/
private theorem large_cost [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (costLaw : RecurseCost call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : Edges before (first :: rest))
    (closed : ClosedEdges (first :: rest)) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.large call clear fuel top first rest before = .done result after) (heap : CostHeap before) : CostHeap after := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have middleHeap := map_cost (SourceMergedWorker.column call clear fuel)
    (fun state values => Values state values ∧ ClosedValues values)
    (fun _ _ effect _ valid => ⟨(fun value member => effect.1.available value (valid.1 value member)), valid.2⟩) columns
    (fun values _ state ready valid result final actual =>
      (SourceMergedColumns.column_done call clear fuel (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law
        values state ready valid.1 valid.2 result final actual).1)
    (fun values _ state ready valid result final actual => column_cost call costLaw clear fuel values state ready valid.1 valid.2 result final actual)
    before semantic (fun column member => ⟨(by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact closed edge outer value inner)⟩) values middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact middleHeap

/-- Both actual source threshold branches preserve the stored cost heap. -/
private theorem group_cost [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (costLaw : RecurseCost call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedWorker.group call clear fuel top edges before = .done results after) (heap : CostHeap before) : CostHeap after := by
  unfold SourceMergedWorker.group at done
  split at done
  · exact map_cost (small call) (fun state edge => EdgeResident state edge ∧ ClosedValues edge.children)
      (fun _ _ effect edge valid => ⟨InternedEdgeResidency.edge_grows _ _ effect.1.growth edge valid.1, valid.2⟩) edges
      (fun edge _ state ready valid result final actual => (SourceMergedEdges.small_done call (fun _ _ => true) (fun _ _ => False) law edge state ready valid.1 valid.2 result final actual).1)
      (fun edge _ state ready valid result final actual => small_cost call law costLaw edge state ready valid.1 valid.2 result final actual)
      before semantic (fun edge member => ⟨resident edge member, closed edge member⟩) results after done heap
  · cases edges with
    | nil => simp at *
    | cons first rest =>
        obtain ⟨result, final, made, returned⟩ := (bind_done _ _ results after).mp done
        have finalHeap := large_cost call law costLaw clear fuel top first rest before semantic resident closed result final made heap
        have parts := Result.done.inj returned
        cases parts.2
        exact finalHeap

/-- Actual ordered groups preserve stored costs before the final node request. -/
private theorem root_cost [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (costLaw : RecurseCost call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (groups : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges groups) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.root call clear fuel top groups before = .done result after) (heap : CostHeap before) : CostHeap after := by
  obtain ⟨rows, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have middleHeap := map_cost (SourceMergedWorker.group call clear fuel top)
    (fun state edges => Edges state edges ∧ ClosedEdges edges)
    (fun _ _ effect _ valid => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.1.growth edge (valid.1 edge member)), valid.2⟩) groups
    (fun group member state ready valid result final actual =>
      (SourceMergedGroups.group_done call clear fuel (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law top (fun _ => rfl)
        group (grouping.keys edges groups group member) state ready valid.1 valid.2 result final actual).1)
    (fun group _ state ready valid result final actual => group_cost call law costLaw clear fuel top group state ready valid.1 valid.2 result final actual)
    before semantic (fun group member => ⟨(fun edge included => resident edge (original group member edge included)),
      (fun edge included => closed edge (original group member edge included))⟩) rows middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact InternedFreshOrdinaryCostHeap.preserve middle _ middleHeap (InternedShallowHeap.makeNode_noNewMu rows.flatten middle)

/-- Every actual successful source merge worker derives stored cost preservation by ordinary-fuel induction. -/
private theorem worker_closed_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinaryFuel comparisonFuel : Nat) :
    RecurseCost (SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel) := by
  induction ordinaryFuel with
  | zero =>
      intro value before semantic available closed result after done heap
      cases value with
      | node entry edges depth free =>
          simp only [Value.free] at closed
          simp only [SourceMergedWorker.worker, closed, ite_true] at done
          cases done
      | empty | reference | mu | union =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap
  | succ remaining ih =>
      intro value before semantic available closed result after done heap
      cases value with
      | node entry edges depth free =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have rowsClosed : ClosedEdges edges := fun edge member child included =>
            MergedOrdinaryHeight.closed_child before facts.coherent entry edges depth free available.resident closed edge member child included
          have law := SourceMergedSoundness.worker_done grouping groupingCorrect clear top (fun _ _ => true) (fun _ _ => False)
            (fun _ _ _ => rfl) (fun _ => rfl) remaining comparisonFuel
          exact root_cost _ law ih clear comparisonFuel top edges (grouping edges) (groupingCorrect edges)
            before semantic resident rowsClosed result after (by simpa only [SourceMergedWorker.worker, show free = [] from closed, ite_true] using done) heap
      | empty | reference | mu | union =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap

/-- The source returns an open root unchanged before ordinary recursion. -/
theorem worker_open [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (clear : Guard → Bool) (top : Guard) (ordinaryFuel comparisonFuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (notClosed : value.free ≠ []) :
    SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel value before = .done value before := by
  cases ordinaryFuel <;> cases value <;> simp_all [SourceMergedWorker.worker, MergedColdMerge.pure, Value.free]

/-- Actual worker completion retains stored costs for open and closed available inputs. -/
theorem worker_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinaryFuel comparisonFuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel value before = .done result after)
    (costs : CostHeap before) : CostHeap after := by
  by_cases closed : value.free = []
  · exact worker_closed_cost_heap grouping groupingCorrect clear top ordinaryFuel comparisonFuel
      value before semantic available closed result after done costs
  · rw [worker_open grouping clear top ordinaryFuel comparisonFuel value before closed] at done
    cases (Result.done.inj done).2
    exact costs

/-- A completed source worker retains complete heaps and its exact available result. -/
theorem worker_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (topValid : annotation top) (ordinaryFuel comparisonFuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (result : Value Symbol Guard)
    (after : State Symbol Guard)
    (done : SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel value before = .done result after) :
    Effect annotation before after ∧ Available after result := by
  have retained := worker_cost_heap grouping groupingCorrect clear top ordinaryFuel comparisonFuel
    value before semantic available result after done costs
  by_cases closed : value.free = []
  · have checked := SourceMergedSoundness.worker_done grouping groupingCorrect clear top
      (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) (fun _ => rfl)
      ordinaryFuel comparisonFuel value before semantic available closed result after done
    exact ⟨⟨checked.1.1, checked.1.2, retained,
      SourceMergedAnnotationWorker.worker_heap annotation grouping groupingCorrect clear top topValid
        ordinaryFuel comparisonFuel value before semantic available closed result after done⟩, checked.2.available⟩
  · rw [worker_open grouping clear top ordinaryFuel comparisonFuel value before closed] at done
    have parts := Result.done.inj done
    cases parts.1; cases parts.2
    exact ⟨⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩, available⟩

/-- Actual executable grouping retains stored costs at its exact returned heap. -/
theorem execute_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.execute clear top fuel value before = .done result after)
    (costs : CostHeap before) : CostHeap after :=
  worker_cost_heap MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top
    (MergedOrdinaryHeight.height value) fuel value before semantic available result after done costs

/-- Source execution retains histories, semantic readiness, costs, and physical annotations. -/
theorem execute_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (topValid : annotation top) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.execute clear top fuel value before = .done result after) :
    Effect annotation before after ∧ Available after result :=
  worker_effect annotation MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top topValid
    (MergedOrdinaryHeight.height value) fuel value before semantic costs available result after done

/-- Actual native merge receipts retain costs without a closed-original premise. -/
theorem merge_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {value result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEqualityNativeMerge.Merge clear top value before result after)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap value) (costs : CostHeap before.machine.heap) :
    CostHeap after.machine.heap := by
  cases trace with
  | done fuel actual =>
      exact execute_cost_heap clear top fuel value before.machine.heap ready.semantic available result _ actual costs

/-- Native merging changes only its actual constructor heap and retains all heap invariants. -/
theorem merge_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {value result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEqualityNativeMerge.Merge clear top value before result after)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap value) (costs : CostHeap before.machine.heap)
    (topValid : annotation top) :
    SourceEqualityNativeScoped.IdleReady emptyGuard conjoin after ∧
      Effect annotation before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | done fuel actual =>
      have checked := execute_effect annotation clear top topValid fuel value before.machine.heap
        ready.semantic costs available result _ actual
      exact ⟨ready.advance _ checked.1.keeps checked.1.semantic, checked.1, checked.2, rfl, rfl, rfl⟩

end MicroCFTA.SourceCurrentMergedHeapEffects
