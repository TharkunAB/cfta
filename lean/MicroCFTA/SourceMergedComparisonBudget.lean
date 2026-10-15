import MicroCFTA.SourceMergedComparisonEffects
import MicroCFTA.MergedFreshOrdinaryColdBudget

/-!
# Finite degree progress of general repaired comparisons

Each successful actual read either reduces unfinished Mu degrees or keeps
the identical cache. Ordered comparison stages compose this progress and
retain the fixed maximum degree. No prepared-body premise is used.
-/
namespace MicroCFTA.SourceMergedComparisonBudget
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (Effect bind_done read_graph)
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open InternedMuDepthInventory (Bounded)
open InternedFreshMuUnfoldBudget (Progress)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A successful comparison stage retains all effects and its exact degree progress. -/
structure Budget (limit : Nat) (before after : State Symbol Guard) : Prop where
  effect : Effect before after
  bounded : Bounded after limit
  progress : Progress limit before after

/-- Ordered successful stages compose degree progress through their actual cache. -/
theorem Budget.trans {limit : Nat} {before middle after : State Symbol Guard}
    (first : Budget limit before middle) (second : Budget limit middle after) : Budget limit before after :=
  ⟨first.effect.trans second.effect, second.bounded, Progress.trans limit before middle after first.progress second.progress⟩

/-- A direct Boolean return retains the fixed bound and exact cache. -/
theorem pure_budget (limit : Nat) (before : State Symbol Guard) (semantic : SemanticReady before) (bounded : Bounded before limit)
    (answer result : Bool) (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) : Budget limit before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨⟨pure_keeps _ semantic.ready, semantic⟩, bounded, Or.inr rfl⟩

/-- An actual successful general read derives degree progress from its physical reader receipt. -/
theorem read_budget (limit fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit) (available : Available before value) (closed : value.free = [])
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done edges after) : Budget limit before after := by
  have trace := read_graph fuel value before edges after done
  have checked := trace.verified semantic available closed
  cases trace with
  | done bound actual =>
      have progress := MergedFreshOrdinaryColdBudget.nodeEdges_progress bound limit value before semantic.ready.semantic semantic.ready.covered
        semantic.ready.depth bounded available closed edges after actual
      exact ⟨⟨checked.1, checked.2.1⟩, progress.2.1, progress.2.2⟩

/-- Successful recursive callbacks retain their fixed degree bound and actual progress. -/
def Callback (limit : Nat) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → Bounded before limit → Available before wide → Available before narrow →
    wide.free = [] → narrow.free = [] → ∀ answer after, compare wide narrow before = .done answer after → Budget limit before after

/-- Successful source zip conjunctions compose every demanded recursive budget. -/
theorem children_budget (limit : Nat) (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback limit compare) (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows) (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) : Budget limit before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_budget limit before semantic bounded true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_budget limit before semantic bounded true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have checked := callback wide narrow before semantic bounded (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
            (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => exact checked.trans (pure_budget limit middle checked.effect.2 checked.bounded false answer after later)
          | true => exact checked.trans (ih narrows middle checked.effect.2 checked.bounded
              (fun value member => checked.effect.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => checked.effect.1.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
              (fun value member => narrowClosed value (List.mem_cons_of_mem _ member)) later)

/-- Ordered cover search retains progress from failed candidates as well as the successful candidate. -/
theorem anyCover_budget [DecidableEq Symbol] (limit : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback limit compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides) (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) : Budget limit before after := by
  induction wides generalizing before with
  | nil => exact pure_budget limit before semantic bounded false answer after done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have checked := children_budget limit compare callback wide.children narrow.children before semantic bounded
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs
          (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
        cases accepted with
        | true => exact checked.trans (pure_budget limit middle checked.effect.2 checked.bounded true answer after later)
        | false => exact checked.trans (ih middle checked.effect.2 checked.bounded
            (fun value member => checked.effect.1.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle checked.effect.1.growth edge (wideInputs edge (List.mem_cons_of_mem _ member)))
            (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) later)
      · exact ih before semantic bounded narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done

/-- Every demanded wide read and cover search retains the exact degree progress for the next row. -/
theorem allRows_budget [DecidableEq Symbol] (limit fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback limit compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows) (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) : Budget limit before after := by
  induction narrows generalizing before with
  | nil => exact pure_budget limit before semantic bounded true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := (read_graph fuel wide before wides readAfter read).verified semantic wideInput wideClosed
      have readBudget := read_budget limit fuel wide before semantic bounded wideInput wideClosed wides readAfter read
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverBudget := anyCover_budget limit clear compare callback narrow wides readAfter readFacts.2.1 readBudget.bounded
        (fun value member => readFacts.1.available value (childInputs value member)) readFacts.2.2.1
        (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted middle covered
      have first := readBudget.trans coverBudget
      cases accepted with
      | false => exact first.trans (pure_budget limit middle first.effect.2 first.bounded false answer after rest)
      | true => exact first.trans (ih middle first.effect.2 first.bounded (first.effect.1.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.effect.1.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member)))
          (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) rest)

/-- Every successful general comparison preserves its fixed maximum degree and exact global progress. -/
theorem check_budget [DecidableEq Symbol] (limit : Nat) (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (wideInput : Available before wide) (narrowInput : Available before narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) : Budget limit before after := by
  rw [check] at done
  split at done
  · exact pure_budget limit before semantic bounded true answer after done
  · split at done
    · exact pure_budget limit before semantic bounded false answer after done
    · split at done
      · exact pure_budget limit before semantic bounded true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_budget limit before semantic bounded true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := (read_graph (fuel + 1) narrow before narrows middle read).verified semantic narrowInput narrowClosed
                      have readBudget := read_budget limit (fuel + 1) narrow before semantic bounded narrowInput narrowClosed narrows middle read
                      have rest := allRows_budget limit (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                        (check_budget limit clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.2.1 readBudget.bounded
                        (readFacts.1.available wide wideInput) readFacts.2.2.1 wideClosed readFacts.2.2.2 answer after later
                      exact readBudget.trans rest
termination_by fuel

end MicroCFTA.SourceMergedComparisonBudget
