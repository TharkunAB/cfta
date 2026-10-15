import MicroCFTA.SourceMergedComparisonEffects
import MicroCFTA.SourceEqualityAnnotationProjection

/-!
# Physical edge annotations through actual general merge comparisons

Each successful comparison retains its actual cache effects and annotation
heap. Repaired row reads derive annotation preservation from actual source
exposure. Ordered cover searches retain every intermediate scope.
-/
namespace MicroCFTA.SourceMergedAnnotationComparison
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonEffects (read_graph bind_done)
open SourceEqualityAnnotationHeap (Heap)

/-- A successful stage retains actual cache effects and preserves physical edge annotations. -/
structure Effect (annotation : Guard → Prop) (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  annotations : Heap annotation before → Heap annotation after

/-- Annotation effects retain the previously proved source cache effects. -/
theorem Effect.original {annotation : Guard → Prop} {before after : State Symbol Guard} (effect : Effect annotation before after) :
    SourceMergedComparisonEffects.Effect before after := ⟨effect.keeps, effect.semantic⟩

/-- A direct Boolean return has no cache effects. -/
theorem pure_effect (annotation : Guard → Prop) (before : State Symbol Guard) (semantic : SemanticReady before) (answer result : Bool)
    (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) : Effect annotation before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨pure_keeps _ semantic.ready, semantic, fun heap => heap⟩

/-- Ordered successful effects compose semantic caches, histories, and annotation preservation. -/
theorem Effect.trans {annotation : Guard → Prop} {before middle after : State Symbol Guard} (first : Effect annotation before middle) (second : Effect annotation middle after) : Effect annotation before after :=
  ⟨first.keeps.trans second.keeps, second.semantic, fun heap => second.annotations (first.annotations heap)⟩

/-- Successful callback effects are local to actual closed available operands and returned states. -/
def Callback (annotation : Guard → Prop) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → Available before wide → Available before narrow → wide.free = [] → narrow.free = [] →
    ∀ answer after, compare wide narrow before = .done answer after → Effect annotation before after

/-- The source zip conjunction preserves annotations even when a list ends early. -/
theorem children_effect (annotation : Guard → Prop) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback annotation compare) (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows) (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) : Effect annotation before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_effect annotation before semantic true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_effect annotation before semantic true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have effect := callback wide narrow before semantic (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
            (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => exact effect.trans (pure_effect annotation middle effect.semantic false answer after later)
          | true => exact effect.trans (ih narrows middle effect.semantic
              (fun value member => effect.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.keeps.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
              (fun value member => narrowClosed value (List.mem_cons_of_mem _ member)) later)

/-- Actual ordered edge-cover search retains semantic cache fields and physical annotations. -/
theorem anyCover_effect (annotation : Guard → Prop) [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback annotation compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides) (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) : Effect annotation before after := by
  induction wides generalizing before with
  | nil => exact pure_effect annotation before semantic false answer after done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effect := children_effect annotation compare callback wide.children narrow.children before semantic
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs
          (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
        cases accepted with
        | true => exact effect.trans (pure_effect annotation middle effect.semantic true answer after later)
        | false => exact effect.trans (ih middle effect.semantic (fun value member => effect.keeps.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.keeps.growth edge (wideInputs edge (List.mem_cons_of_mem _ member)))
            (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) later)
      · exact ih before semantic narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done

/-- Each actual row read and cover search retains annotations and the next input scope. -/
theorem allRows_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback annotation compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows) (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) : Effect annotation before after := by
  induction narrows generalizing before with
  | nil => exact pure_effect annotation before semantic true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := (read_graph fuel wide before wides readAfter read).verified semantic wideInput wideClosed
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverFacts := anyCover_effect annotation clear compare callback narrow wides readAfter readFacts.2.1
        (fun value member => readFacts.1.available value (childInputs value member)) readFacts.2.2.1
        (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted middle covered
      have first : Effect annotation before middle := ⟨readFacts.1.trans coverFacts.keeps, coverFacts.semantic,
        fun heap => coverFacts.annotations (SourceEqualityAnnotationProjection.read annotation (read_graph fuel wide before wides readAfter read)
          semantic wideInput wideClosed heap)⟩
      cases accepted with
      | false => exact first.trans (pure_effect annotation middle first.semantic false answer after rest)
      | true => exact first.trans (ih middle first.semantic (first.keeps.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.keeps.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member)))
          (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) rest)

/-- Every completed general repaired comparison derives annotation and semantic cache preservation. -/
theorem check_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInput : Available before narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) : Effect annotation before after := by
  rw [check] at done
  split at done
  · exact pure_effect annotation before semantic true answer after done
  · split at done
    · exact pure_effect annotation before semantic false answer after done
    · split at done
      · exact pure_effect annotation before semantic true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_effect annotation before semantic true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := (read_graph (fuel + 1) narrow before narrows middle read).verified semantic narrowInput narrowClosed
                      have rest := allRows_effect annotation (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                        (check_effect annotation clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.2.1
                        (readFacts.1.available wide wideInput) readFacts.2.2.1 wideClosed readFacts.2.2.2 answer after later
                      exact ⟨readFacts.1.trans rest.keeps, rest.semantic,
                        fun heap => rest.annotations (SourceEqualityAnnotationProjection.read annotation (read_graph (fuel + 1) narrow before narrows middle read)
                          semantic narrowInput narrowClosed heap)⟩
termination_by fuel

end MicroCFTA.SourceMergedAnnotationComparison
