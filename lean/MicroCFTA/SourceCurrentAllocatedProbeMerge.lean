import MicroCFTA.SourceCurrentAllocatedProbeExposure
import MicroCFTA.SourceCurrentAllocatedMergePhysical

/-!
# Filtered probes through actual comparison and merge

Comparison follows its completed reads and short circuits. The recursive
merge proof follows the actual memo-aware call graph. Constructor branches
introduce no Mu records. Stored unfolding retains probes through its build.
No result-probe premise is required at recursive requests.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeMerge
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonEffects (bind_done)
open InternedFreshOrdinaryProbeHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A successful stage retains actual cache effects and preserves physical edge probes. -/
structure Effect (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  probes : Heap before → Heap after

/-- Annotation effects retain the previously proved source cache effects. -/
theorem Effect.original {before after : State Symbol Guard} (effect : Effect before after) :
    SourceMergedComparisonEffects.Effect before after := ⟨effect.keeps, effect.semantic⟩

/-- A direct Boolean return has no cache effects. -/
theorem pure_effect (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) (answer result : Bool)
    (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) : Effect before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩

/-- Ordered successful effects compose semantic caches, histories, and probe preservation. -/
theorem Effect.trans {before middle after : State Symbol Guard} (first : Effect before middle) (second : Effect middle after) : Effect before after :=
  ⟨first.keeps.trans second.keeps, second.semantic, second.costs, fun heap => second.probes (first.probes heap)⟩

/-- A completed actual row read retains both heaps and returns resident rows. -/
theorem read_effect [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after) :
    Effect before after ∧ Edges after rows := by
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
        SourceCurrentAllocatedProbeExposure.nodeEdges_heap fuel value before semantic heap available
  | pending | unresolved | exhausted =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      cases done

/-- Callback effects use only actual available operands and their current heaps. -/
def Callback (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → CostHeap before → Available before wide → Available before narrow →
    ∀ answer after, compare wide narrow before = .done answer after → Effect before after

/-- The source zip conjunction preserves probes even when a list ends early. -/
theorem children_effect (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) : Effect before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_effect before semantic costs true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_effect before semantic costs true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have effect := callback wide narrow before semantic costs (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => exact effect.trans (pure_effect middle effect.semantic effect.costs false answer after later)
          | true => exact effect.trans (ih narrows middle effect.semantic effect.costs
              (fun value member => effect.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.keeps.available value (narrowInputs value (List.mem_cons_of_mem _ member))) later)

/-- Actual ordered edge-cover search retains semantic cache fields and physical probes. -/
theorem anyCover_effect [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) : Effect before after := by
  induction wides generalizing before with
  | nil => exact pure_effect before semantic costs false answer after done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effect := children_effect compare callback wide.children narrow.children before semantic costs
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs accepted middle first
        cases accepted with
        | true => exact effect.trans (pure_effect middle effect.semantic effect.costs true answer after later)
        | false => exact effect.trans (ih middle effect.semantic effect.costs (fun value member => effect.keeps.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.keeps.growth edge (wideInputs edge (List.mem_cons_of_mem _ member))) later)
      · exact ih before semantic costs narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member)) done

/-- Each actual row read and cover search retains probes and the next input scope. -/
theorem allRows_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) : Effect before after := by
  induction narrows generalizing before with
  | nil => exact pure_effect before semantic costs true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := read_effect fuel wide before semantic costs wideInput wides readAfter read
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverFacts := anyCover_effect clear compare callback narrow wides readAfter readFacts.1.semantic readFacts.1.costs
        (fun value member => readFacts.1.keeps.available value (childInputs value member)) readFacts.2 accepted middle covered
      have first : Effect before middle := readFacts.1.trans coverFacts
      cases accepted with
      | false => exact first.trans (pure_effect middle first.semantic first.costs false answer after rest)
      | true => exact first.trans (ih middle first.semantic first.costs (first.keeps.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.keeps.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member))) rest)

/-- Every completed structural comparison retains costs and probes on available open or closed operands. -/
theorem check_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) : Effect before after := by
  rw [check] at done
  split at done
  · exact pure_effect before semantic costs true answer after done
  · split at done
    · exact pure_effect before semantic costs false answer after done
    · split at done
      · exact pure_effect before semantic costs true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_effect before semantic costs true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := read_effect (fuel + 1) narrow before semantic costs narrowInput narrows middle read
                      have rest := allRows_effect (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                        (check_effect clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.1.semantic readFacts.1.costs
                        (readFacts.1.keeps.available wide wideInput) readFacts.2 answer after later
                      exact readFacts.1.trans rest
termination_by fuel


open MergedPhysicalGroupColumns (closedMu)

/-- Every completed recursive-cover scan retains probes and actual cache histories. -/
theorem anyAccepts_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (answer : Bool) (after : State Symbol Guard) (done : SourceMergedSelection.anyAccepts clear fuel narrow wides before = .done answer after) : Effect before after := by
  induction wides generalizing before with
  | nil => exact pure_effect before semantic costs false answer after done
  | cons wide wides ih =>
      by_cases narrowClosed : narrow.free = []
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_true] at done
        obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effects := check_effect clear fuel [] wide narrow before semantic costs (wideInputs _ List.mem_cons_self) narrowInput accepted middle first
        cases accepted with
        | true => exact effects.trans (pure_effect middle effects.semantic effects.costs true answer after later)
        | false => exact effects.trans (ih middle effects.semantic effects.costs (effects.keeps.available narrow narrowInput)
            (fun value member => effects.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member))) later)
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_false] at done
        exact pure_effect before semantic costs false answer after done

/-- Successful actual filtering retains probe heaps, semantic heaps, and both histories. -/
theorem retain_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (recInputs : Values before recursive) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.retain clear fuel recursive inputs before = .done retained after) : Effect before after := by
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
        have effects := anyAccepts_effect clear fuel child recursive before semantic costs (available _ List.mem_cons_self) recInputs covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have parts := Result.done.inj returned
        cases parts.2
        exact effects.trans (ih middle effects.semantic effects.costs (fun value member => effects.keeps.available value (recInputs value member))
          (fun value member => effects.keeps.available value (available value (List.mem_cons_of_mem _ member))) rest after tail)

/-- The actual retention and identity filter preserve probes at the returned cache. -/
theorem select_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done retained after) : Effect before after := by
  obtain ⟨values, middle, filtered, returned⟩ := (bind_done _ _ retained after).mp done
  have checked := retain_effect clear fuel (inputs.filter closedMu) inputs before semantic costs
    (fun value member => available value (List.mem_filter.mp member).1) available values middle filtered
  have parts := Result.done.inj returned
  cases parts.2
  exact checked



namespace Merge
open SourceCurrentMemoMergeGraph
namespace Physical
export SourceCurrentMemoMergeEffects (Stored Contract Certified Effect run_effects body_certified)
end Physical
open InternedShallowHeap (NoNewMu)

private def Ordinary [DecidableEq (EdgeKey Symbol Guard)] : Code Symbol Guard Output → Prop
  | .pure _ | .select _ | .request _ => True
  | .work job => ∀ state, NoNewMu state (run job state).2
  | .bind first next => Ordinary first ∧ ∀ value, Ordinary (next value)

private theorem map_ordinary [DecidableEq (EdgeKey Symbol Guard)] (call : Input → Code Symbol Guard Output) (inputs : List Input)
    (safe : ∀ input ∈ inputs, Ordinary (call input)) : Ordinary (map call inputs) := by
  induction inputs with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨safe first List.mem_cons_self, fun _ =>
        ⟨ih (fun input member => safe input (List.mem_cons_of_mem _ member)), fun _ => trivial⟩⟩

private theorem edge_ordinary [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard)) :
    Ordinary (.work (makeEdge symbol guard children)) := by
  intro state
  exact InternedShallowHeap.noNewMu_refl state

private theorem node_ordinary [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard)) :
    Ordinary (.work (makeNode edges)) := InternedShallowHeap.makeNode_noNewMu edges

private theorem union_ordinary [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard)) :
    Ordinary (.work (makeUnion values)) := InternedShallowHeap.makeUnion_noNewMu values

private theorem retained_ordinary [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard)) :
    Ordinary (retainedColumn values) := by
  have general (values : List (Value Symbol Guard)) :
      Ordinary (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
        else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) := by
    split
    · exact union_ordinary values
    · exact ⟨node_ordinary _, fun _ => trivial⟩
  cases values with
  | nil => exact general []
  | cons first rest => cases rest with
    | nil => trivial
    | cons second rest => exact general (first :: second :: rest)

private theorem small_ordinary [DecidableEq (EdgeKey Symbol Guard)] (edge : EdgeValue Symbol Guard) :
    Ordinary (small edge) :=
  ⟨map_ordinary Code.request edge.children (by intros; trivial), fun _ => edge_ordinary _ _ _⟩

private theorem column_ordinary [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard)) :
    Ordinary (column values) := ⟨trivial, retained_ordinary⟩

private theorem large_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Ordinary (large top first rest) :=
  ⟨map_ordinary column _ (fun _ _ => column_ordinary _), fun _ => edge_ordinary _ _ _⟩

private theorem group_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (edges : List (EdgeValue Symbol Guard)) : Ordinary (group top edges) := by
  unfold group
  split
  · exact map_ordinary small edges (fun _ _ => small_ordinary _)
  · split
    · trivial
    · exact ⟨large_ordinary _ _ _, fun _ => trivial⟩

private theorem root_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (groups : List (List (EdgeValue Symbol Guard))) : Ordinary (root top groups) :=
  ⟨map_ordinary (group top) groups (fun _ _ => group_ordinary _ _), fun _ => node_ordinary _⟩

private theorem body_ordinary [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (input : Value Symbol Guard) : Ordinary (body top input) := by
  cases input with
  | node entry edges depth free =>
      change Ordinary (if free = [] then root top (MergedSourceGrouping.groups edges) else .pure (.node entry edges depth free))
      split
      · exact root_ordinary _ _
      · trivial
  | empty | reference | union | mu => trivial

private theorem run_preserves [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Physical.Stored before memo →
      Physical.Certified Physical.Contract clear code before post → Ordinary code → Heap before → Heap after := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => SemanticReady before → CostHeap before →
        Physical.Stored before memo → Available before input → Heap before → Heap after) with
  | pure value state memo =>
      intro post semantic costs stored checked ordinary probes
      exact probes
  | work job state memo =>
      intro post semantic costs stored checked ordinary probes
      exact InternedFreshOrdinaryProbeHeap.preserve _ _ probes (ordinary state)
  | select fuel done =>
      intro post semantic costs stored checked ordinary probes
      exact (select_effect _ fuel _ _ semantic costs checked.1 _ _ done).probes probes
  | request actual ih =>
      intro post semantic costs stored checked ordinary probes
      exact ih semantic costs stored checked.1 probes
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored checked ordinary probes
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      have middleProbes := ihFirst intermediate semantic costs stored firstChecked ordinary.1 probes
      obtain ⟨effect, retained, valid⟩ := Physical.run_effects first intermediate semantic costs stored firstChecked
      exact ihLater post effect.semantic effect.costs retained (nextChecked _ _ effect valid) (ordinary.2 _) middleProbes
  | hit found =>
      rename_i semantic costs stored available probes
      exact probes
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored available probes
      exact ih _ semantic costs stored (Physical.body_certified clear top input before semantic costs available)
        (body_ordinary top input) probes

/-- Completed memo-aware calls derive probes through every actual recursive body. -/
theorem call_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Physical.Stored before memo) (available : Available before input)
    (probes : Heap before) : Heap after :=
  run_preserves (.request actual) (fun after output => Physical.Contract input before output after)
    semantic costs stored ⟨available, fun _ _ _ returned => returned⟩ trivial probes

end Merge

/-- Separate Top allocation does not change the heap erased by the actual merge graph. -/
theorem allocated_call_heap [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {clear : SourceSymbolicIndex.Constraint FullSyntax.Formula → Bool}
    {input output : Value (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula)}
    {before after : SourceCurrentAllocatedMergeGraph.State} {memo saved : SourceCurrentAllocatedMergeGraph.Memo}
    (actual : SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (stored : SourceCurrentMemoMergeEffects.Stored before.heap memo) (available : Available before.heap input)
    (probes : Heap before.heap) : Heap after.heap :=
  Merge.call_heap actual.graph ready.semantic ready.costs stored available probes

end MicroCFTA.SourceCurrentAllocatedProbeMerge
