import MicroCFTA.MergedFreshOrdinaryComparison
import MicroCFTA.SourceEqualityProjectionRead

/-!
# General repaired comparison cache effects

Successful comparisons on closed available inputs retain complete semantic
heaps and both constructor histories. Actual repaired reads can allocate Mu
records. No prepared-body or unchanged-cache premise is used.
-/
namespace MicroCFTA.SourceMergedComparisonEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)

/-- Every successful stage retains histories and all next-read semantic premises. -/
def Effect (before after : State Symbol Guard) : Prop := Keeps before after ∧ SemanticReady after

/-- A direct Boolean return has no cache effects. -/
theorem pure_effect (before : State Symbol Guard) (semantic : SemanticReady before) (answer result : Bool)
    (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) : Effect before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨pure_keeps _ semantic.ready, semantic⟩

/-- Ordered successful effects compose complete semantic caches and histories. -/
theorem Effect.trans {before middle after : State Symbol Guard} (first : Effect before middle) (second : Effect middle after) : Effect before after :=
  ⟨first.1.trans second.1, second.2⟩

/-- Completed result sequencing retains the exact first result and continuation. -/
theorem bind_done (first : Result Symbol Guard A) (next : A → State Symbol Guard → Result Symbol Guard B)
    (result : B) (after : State Symbol Guard) :
    first.bind next = .done result after ↔ ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro done; exact ⟨value, state, rfl, done⟩
      · rintro ⟨actual, middle, same, done⟩; cases same; exact done
  | failed => simp [Result.bind]

/-- A successful repaired comparison read is the literal completed cold row read. -/
theorem read_graph [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done edges after) : SourceEqualityProjectionRead.Read value before edges after := by
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows final =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact .done fuel actual
  | pending | unresolved | exhausted => simp only [MergedFreshOrdinaryExposure.read, actual] at done; cases done

/-- Successful callback effects are local to actual closed available operands and returned states. -/
def Callback (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → Available before wide → Available before narrow → wide.free = [] → narrow.free = [] →
    ∀ answer after, compare wide narrow before = .done answer after → Effect before after

/-- The source zip conjunction preserves caches even when a list ends early. -/
theorem children_effect (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows) (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) : Effect before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_effect before semantic true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_effect before semantic true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have effect := callback wide narrow before semantic (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
            (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => exact effect.trans (pure_effect middle effect.2 false answer after later)
          | true => exact effect.trans (ih narrows middle effect.2
              (fun value member => effect.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.1.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
              (fun value member => narrowClosed value (List.mem_cons_of_mem _ member)) later)

/-- Actual ordered edge-cover search retains all semantic cache fields. -/
theorem anyCover_effect [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides) (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) : Effect before after := by
  induction wides generalizing before with
  | nil => exact pure_effect before semantic false answer after done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effect := children_effect compare callback wide.children narrow.children before semantic
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs
          (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
        cases accepted with
        | true => exact effect.trans (pure_effect middle effect.2 true answer after later)
        | false => exact effect.trans (ih middle effect.2 (fun value member => effect.1.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.1.growth edge (wideInputs edge (List.mem_cons_of_mem _ member)))
            (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) later)
      · exact ih before semantic narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done

/-- Each actual wide-row read and cover search retains the premises for the next narrow row. -/
theorem allRows_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows) (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) : Effect before after := by
  induction narrows generalizing before with
  | nil => exact pure_effect before semantic true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := (read_graph fuel wide before wides readAfter read).verified semantic wideInput wideClosed
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverFacts := anyCover_effect clear compare callback narrow wides readAfter readFacts.2.1
        (fun value member => readFacts.1.available value (childInputs value member)) readFacts.2.2.1
        (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted middle covered
      have first : Effect before middle := ⟨readFacts.1.trans coverFacts.1, coverFacts.2⟩
      cases accepted with
      | false => exact first.trans (pure_effect middle first.2 false answer after rest)
      | true => exact first.trans (ih middle first.2 (first.1.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.1.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member)))
          (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) rest)

/-- Every completed general repaired comparison derives complete semantic cache preservation. -/
theorem check_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInput : Available before narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) : Effect before after := by
  rw [check] at done
  split at done
  · exact pure_effect before semantic true answer after done
  · split at done
    · exact pure_effect before semantic false answer after done
    · split at done
      · exact pure_effect before semantic true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_effect before semantic true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := (read_graph (fuel + 1) narrow before narrows middle read).verified semantic narrowInput narrowClosed
                      have rest := allRows_effect (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                        (check_effect clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.2.1
                        (readFacts.1.available wide wideInput) readFacts.2.2.1 wideClosed readFacts.2.2.2 answer after later
                      exact ⟨readFacts.1.trans rest.1, rest.2⟩
termination_by fuel

end MicroCFTA.SourceMergedComparisonEffects
