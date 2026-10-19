import MicroCFTA.SourceCurrentRequiredPublicationHistory
import MicroCFTA.SourceCurrentAllocatedMerge

/-!
# Physical publication history through actual merge calls

Literal selection comparisons retain their actual row reads and unfolds.
The merge graph follows those comparisons and its constructor-only work.
No heap-growth or native memo history implies publication history.
-/
namespace MicroCFTA.SourceCurrentMergePublicationHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonEffects (bind_done)
open SourceCurrentNativeMuPublication (History)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

private structure Effect (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  publication : Nonempty (History before after)

private theorem pure_effect (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (answer result : Bool) (after : State Symbol Guard)
    (done : Result.done answer before = Result.done result after) : Effect before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨pure_keeps _ semantic.ready,semantic,costs,⟨.refl _⟩⟩

private theorem Effect.trans {before middle after : State Symbol Guard}
    (first : Effect before middle) (second : Effect middle after) : Effect before after := by
  obtain ⟨one⟩ := first.publication
  obtain ⟨two⟩ := second.publication
  exact ⟨first.keeps.trans second.keeps,second.semantic,second.costs,⟨.trans one two⟩⟩

private theorem read_effect [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after) :
    Effect before after ∧ Edges after rows := by
  have checked := SourceCurrentMergedHeapEffects.read_effect (fun _ => True)
    fuel value before semantic costs available rows after done
  have actual := SourceMergedComparisonEffects.read_graph fuel value before rows after done
  exact ⟨⟨checked.1.keeps,checked.1.semantic,checked.1.costs,
    SourceCurrentRequiredPublicationHistory.read actual semantic costs available⟩,checked.2⟩

/-- Callback effects use only actual available operands and their current heaps. -/
private def Callback (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → CostHeap before → Available before wide → Available before narrow →
    ∀ answer after, compare wide narrow before = .done answer after → Effect before after

/-- The source zip conjunction preserves publication histories even when a list ends early. -/
private theorem children_effect (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
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

/-- Actual ordered edge-cover search retains semantic cache fields and physical publication histories. -/
private theorem anyCover_effect [DecidableEq Symbol] (clear : Guard → Bool)
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

/-- Each actual row read and cover search retains publication histories and the next input scope. -/
private theorem allRows_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
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

/-- Every completed structural comparison retains costs and publication histories on available open or closed operands. -/
private theorem check_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
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

/-- Every completed recursive-cover scan retains publication histories and actual cache histories. -/
private theorem anyAccepts_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
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

/-- Actual filtering retains publication histories, semantic heaps, and stored costs. -/
private theorem retain_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (recInputs : Values before recursive) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.retain clear fuel recursive inputs before = .done retained after) : Effect before after := by
  induction inputs generalizing before retained after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact ⟨pure_keeps _ semantic.ready, semantic, costs, ⟨.refl _⟩⟩
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

/-- The actual retention and identity filter preserve publication histories at the returned cache. -/
private theorem select_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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


open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Stored Contract Certified run_effects body_certified)

private def Safe : Code Symbol Guard Output → Prop
  | .pure _ => True
  | .work job => ∀ heap, InternedShallowHeap.NoNewMu heap (run job heap).2
  | .select _ | .request _ => True
  | .bind first next => Safe first ∧ ∀ value, Safe (next value)

private theorem safe_map (call : Input → Code Symbol Guard Output) (inputs : List Input)
    (safe : ∀ input, Safe (call input)) : Safe (SourceCurrentMemoMergeGraph.map call inputs) := by
  induction inputs with
  | nil => trivial
  | cons first rest ih => exact ⟨safe first,fun _ => ⟨ih,fun _ => trivial⟩⟩

private theorem safe_retained (values : List (Value Symbol Guard)) : Safe (retainedColumn values) := by
  have branches (values : List (Value Symbol Guard)) :
      Safe (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
        else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) := by
    split
    · exact fun heap => InternedShallowHeap.makeUnion_noNewMu values heap
    · exact ⟨fun heap => InternedShallowHeap.makeNode_noNewMu _ heap,fun _ => trivial⟩
  cases values with
  | nil => exact branches []
  | cons first rest =>
    cases rest with
    | nil => trivial
    | cons second rest => exact branches (first :: second :: rest)

private theorem safe_small (edge : EdgeValue Symbol Guard) : Safe (small edge) :=
  ⟨safe_map Code.request edge.children (fun _ => trivial),fun _ => fun _ => InternedShallowHeap.noNewMu_refl _⟩

private theorem safe_large (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Safe (large top first rest) :=
  ⟨safe_map column _ (fun _ => ⟨trivial,safe_retained⟩),
    fun _ => fun _ => InternedShallowHeap.noNewMu_refl _⟩

private theorem safe_group (top : Guard) (edges : List (EdgeValue Symbol Guard)) : Safe (group top edges) := by
  unfold group
  split
  · exact safe_map small edges safe_small
  · cases edges with
    | nil => trivial
    | cons first rest => exact ⟨safe_large top first rest,fun _ => trivial⟩

private theorem safe_body [DecidableEq Symbol]
    (top : Guard) (input : Value Symbol Guard) : Safe (body top input) := by
  cases input with
  | node entry edges depth free =>
    by_cases closed : free = []
    · simp only [body,closed,ite_true]
      exact ⟨safe_map (group top) _ (safe_group top),fun _ => InternedShallowHeap.makeNode_noNewMu _⟩
    · simp only [body,closed,ite_false]
      trivial
  | empty | reference | union | mu => trivial

private theorem run_history [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ post, SemanticReady before → CostHeap before → Stored before memo →
      Certified Contract clear code before post → Safe code → Nonempty (History before after) := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => SemanticReady before → CostHeap before →
        Stored before memo → Available before input → Nonempty (History before after)) with
  | pure => intros; exact ⟨.refl _⟩
  | work job heap memo =>
    intro post semantic costs stored checked safe
    exact ⟨.retain _ _ (safe heap)⟩
  | select fuel done =>
    intro post semantic costs stored checked safe
    exact (select_effect _ fuel _ _ semantic costs checked.1 _ _ done).publication
  | request actual ih =>
    intro post semantic costs stored checked safe
    exact ih semantic costs stored checked.1
  | bind first later ihFirst ihLater =>
    intro post semantic costs stored checked safe
    obtain ⟨intermediate,firstChecked,nextChecked⟩ := checked
    obtain ⟨firstEffect,firstStored,returned⟩ := run_effects first intermediate semantic costs stored firstChecked
    obtain ⟨firstHistory⟩ := ihFirst intermediate semantic costs stored firstChecked safe.1
    obtain ⟨laterHistory⟩ := ihLater post firstEffect.semantic firstEffect.costs firstStored
      (nextChecked _ _ firstEffect returned) (safe.2 _)
    exact ⟨.trans firstHistory laterHistory⟩
  | hit => intros; exact ⟨.refl _⟩
  | miss absent actual ih =>
    rename_i semantic costs stored available
    exact ih _ semantic costs stored (body_certified _ _ _ _ semantic costs available) (safe_body _ _)

/-- Every completed memo merge follows actual comparison reads and constructor publication effects. -/
theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    Nonempty (History before after) :=
  run_history (.request actual) (fun after output => Contract input before output after) semantic costs stored
    ⟨available,fun _ _ _ returned => returned⟩ trivial

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- The allocated receipt preserves physical publication history at its exact checked return heap. -/
theorem merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas solver inventory clear input before memo output after saved memos final}
    (receipt : SourceCurrentAllocatedMerge.Receipt (width := width) formulas solver inventory clear
      input before memo output after saved memos final)
    (semantic : SemanticReady before.native.machine.heap) (costs : CostHeap before.native.machine.heap)
    (stored : Stored before.native.machine.heap memo) (available : Available before.native.machine.heap input) :
    Nonempty (History before.native.machine.heap after.native.machine.heap) := by
  cases receipt.actual with
  | done actual => exact call actual.graph semantic costs stored available

end MicroCFTA.SourceCurrentMergePublicationHistory
