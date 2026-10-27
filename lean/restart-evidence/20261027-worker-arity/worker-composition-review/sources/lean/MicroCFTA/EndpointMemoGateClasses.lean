import MicroCFTA.EndpointMemoGateLift
import MicroCFTA.EndpointStatefulGateCompletion

/-!
# Enabled primary gate paths and classes with three memo families

Actual path and class workers use the enabled endpoint policy. False paths
pass their returned constructor heap and all three memo tables to the next
path. A true path omits the remaining class suffix. These are completed
call receipts. They do not force a complete primary partition or transfer
the receipts to GHC thunk publication and concurrent cache ownership.
-/
namespace MicroCFTA.EndpointStatefulGateTrace
open InternedConstructorTemplates InternedNestedConstruction EqualityNormalize
open EndpointStatefulGate
open InternedFreshOrdinaryStatefulGate (anyKnown)

/-- A source forest path is empty or follows its exact selected original child. -/
inductive PathTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Path → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | empty : PathTrace unconstrained reaches values [] state false state
  | child (trace : ChildTrace unconstrained reaches values index rest state answer final) :
      PathTrace unconstrained reaches values (index :: rest) state answer final

/-- The primary class scans original paths in order and stops at its first true result. -/
inductive ClassTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Class → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | nil : ClassTrace unconstrained reaches values [] state false state
  | stop (head : PathTrace unconstrained reaches values path state true final) :
      ClassTrace unconstrained reaches values (path :: rest) state true final
  | next (head : PathTrace unconstrained reaches values path state false middle)
      (tail : ClassTrace unconstrained reaches values rest middle answer final) :
      ClassTrace unconstrained reaches values (path :: rest) state answer final

/-- Each completed enabled path worker derives its exact logical graph. -/
theorem path_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : meets unconstrained reaches fuel values path state = .done (some answer) final) :
    PathTrace unconstrained reaches values path state answer final := by
  cases path with
  | nil =>
      simp only [meets, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .empty
  | cons index rest =>
      exact .child (child_trace_of_done unconstrained reaches fuel (node_trace_of_done unconstrained reaches fuel)
        values index rest state answer final done)

/-- Each logical enabled path graph derives finite execution with its exact returned heap. -/
theorem path_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : PathTrace unconstrained reaches values path state answer final) :
    ∃ fuel, meets unconstrained reaches fuel values path state = .done (some answer) final := by
  cases trace with
  | empty => exact ⟨0, rfl⟩
  | child trace => exact child_trace_complete _ _ _ _ _ _ _ _ trace

/-- Completed enabled class execution retains each demanded original path and returned heap. -/
theorem class_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : classMeets unconstrained reaches fuel values paths state = .done (some answer) final) :
    ClassTrace unconstrained reaches values paths state answer final := by
  induction paths generalizing state with
  | nil =>
      simp only [classMeets, anyKnown, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .nil
  | cons first rest ih =>
      cases found : meets unconstrained reaches fuel values first state with
      | pending key after => simp [classMeets, anyKnown, found, Outcome.bind] at done
      | done result after =>
          cases result with
          | none => simp [classMeets, anyKnown, found, Outcome.bind] at done
          | some result =>
              have head := path_trace_of_done unconstrained reaches fuel values first state result after found
              cases result with
              | false => exact .next head (ih after (by simpa only [classMeets, anyKnown, found, Outcome.bind] using done))
              | true =>
                  simp only [classMeets, anyKnown, found, Outcome.bind, Outcome.done.injEq, Option.some.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .stop head

/-- Every logical enabled class graph derives finite execution with the same complete heap. -/
theorem class_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : ClassTrace unconstrained reaches values paths state answer final) :
    ∃ fuel, classMeets unconstrained reaches fuel values paths state = .done (some answer) final := by
  induction trace with
  | nil => exact ⟨0, rfl⟩
  | stop head =>
      obtain ⟨fuel, done⟩ := path_trace_complete _ _ _ _ _ _ _ head
      exact ⟨fuel, by simp only [classMeets, anyKnown, done, Outcome.bind]⟩
  | next head tail ih =>
      obtain ⟨headFuel, headDone⟩ := path_trace_complete _ _ _ _ _ _ _ head
      obtain ⟨tailFuel, tailDone⟩ := ih
      have headMore := meets_fuel_stable unconstrained reaches headFuel tailFuel _ _ _ _ _ headDone
      have tailMore := class_fuel_stable unconstrained reaches tailFuel headFuel _ _ _ _ _ tailDone
      refine ⟨headFuel + tailFuel, ?_⟩
      simpa only [classMeets, anyKnown, headMore, Outcome.bind, Nat.add_comm] using tailMore

/-- Enabled logical class graphs are exactly finite completed current-policy execution. -/
theorem class_trace_iff [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) :
    ClassTrace unconstrained reaches values paths state answer final ↔
      ∃ fuel, classMeets unconstrained reaches fuel values paths state = .done (some answer) final := by
  constructor
  · exact class_trace_complete unconstrained reaches values paths state answer final
  · rintro ⟨fuel, done⟩
    exact class_trace_of_done unconstrained reaches fuel values paths state answer final done

/-- Enabled class graphs return one Boolean and one complete constructor heap. -/
theorem class_trace_unique [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (first second : Bool) (firstState secondState : State Symbol Guard)
    (left : ClassTrace unconstrained reaches values paths state first firstState)
    (right : ClassTrace unconstrained reaches values paths state second secondState) :
    first = second ∧ firstState = secondState := by
  obtain ⟨leftFuel, leftDone⟩ := class_trace_complete _ _ _ _ _ _ _ left
  obtain ⟨rightFuel, rightDone⟩ := class_trace_complete _ _ _ _ _ _ _ right
  have leftMore := class_fuel_stable unconstrained reaches leftFuel rightFuel _ _ _ _ _ leftDone
  have rightMore := class_fuel_stable unconstrained reaches rightFuel leftFuel _ _ _ _ _ rightDone
  have same := leftMore.symm.trans (by simpa only [Nat.add_comm] using rightMore)
  simpa only [Outcome.done.injEq, Option.some.injEq] using same

end MicroCFTA.EndpointStatefulGateTrace

namespace MicroCFTA.EndpointMemoGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- A primary path retains all three exact returned memo tables. -/
inductive PathReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {path : Path} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    EndpointStatefulGateTrace.PathTrace source reaches values path state answer final → Memos → Memos → Prop where
  | empty : PathReads .empty memos memos
  | child (trace : ChildReads childTrace memos saved) : PathReads (.child childTrace) memos saved

/-- Primary false paths pass all three tables onward; true paths omit the suffix. -/
inductive ClassReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {paths : Class} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    EndpointStatefulGateTrace.ClassTrace source reaches values paths state answer final → Memos → Memos → Prop where
  | nil : ClassReads .nil memos memos
  | stop (head : PathReads headTrace memos saved) : ClassReads (.stop headTrace) memos saved
  | next (head : PathReads headTrace memos middle) (tail : ClassReads tailTrace middle saved) :
      ClassReads (.next headTrace tailTrace) memos saved

/-- Each completed primary path derives actual coherent calls for all three memo families. -/
theorem lift_path [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : EndpointStatefulGateTrace.PathTrace source reaches values path state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, PathReads trace memos saved ∧ Keeps state final saved := by
  cases trace with
  | empty => exact ⟨memos, .empty, pure_keeps _ _ ready valid⟩
  | child trace =>
      obtain ⟨saved, actual, kept⟩ := lift_child _ _ _ _ _ _ trace ready available memos valid
      exact ⟨saved, .child actual, kept⟩

/-- Each completed primary class derives actual memo calls and ordered constructor effects. -/
theorem lift_class [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, ClassReads trace memos saved ∧ Keeps state final saved := by
  revert valid memos available ready
  induction trace with
  | nil => intro ready available memos valid; exact ⟨memos, .nil, pure_keeps _ _ ready valid⟩
  | stop head =>
      intro ready available memos valid
      obtain ⟨saved, actual, kept⟩ := lift_path _ _ _ _ _ head ready available memos valid
      exact ⟨saved, .stop actual, kept⟩
  | next head tail ih =>
      intro ready available memos valid
      obtain ⟨middle, first, firstKept⟩ := lift_path _ _ _ _ _ head ready available memos valid
      obtain ⟨saved, rest, restKept⟩ := ih firstKept.ready
        (fun value member => (available value member).grows _ _ firstKept.growth firstKept.history)
        middle firstKept.valid
      exact ⟨saved, .next first rest, prepend_keeps firstKept restKept⟩

/-- An actual completed primary worker derives its exact graph and all three returned memo families. -/
theorem completed_class [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (actual : EndpointStatefulGate.classMeets source reaches fuel values paths state = .done (some answer) final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths state answer final,
      ∃ saved, ClassReads trace memos saved ∧ Keeps state final saved := by
  let trace := EndpointStatefulGateTrace.class_trace_of_done source reaches fuel values paths state answer final actual
  obtain ⟨saved, reads, kept⟩ := lift_class _ _ _ _ _ trace ready available memos valid
  exact ⟨trace, saved, reads, kept⟩

/-- Current certified inputs derive finite stable primary class execution with all three actual memo receipts. -/
theorem complete_class [DecidableEq (EdgeKey Symbol Guard)]
    (node : InternedFreshOrdinaryGateRank.Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class)
    (memos : Memos) (valid : Valid node.state memos) :
    ∃ bound answer, ∃ after : InternedFreshOrdinaryGateRank.Node Symbol Guard,
      ∃ trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths node.state answer after.state,
        ∃ saved, ClassReads trace memos saved ∧ Keeps node.state after.state saved ∧
          ∀ extra, EndpointStatefulGate.classMeets source reaches (bound + extra) values paths node.state =
            .done (some answer) after.state := by
  obtain ⟨bound, answer, after, _, _, stable⟩ :=
    EndpointStatefulGateCompletion.class_eventually_exact source reaches node values available paths
  have done := stable 0
  rw [Nat.add_zero] at done
  obtain ⟨trace, saved, reads, kept⟩ := completed_class bound values paths node.state answer after.state
    done (node_ready node) available memos valid
  exact ⟨bound, answer, after, trace, saved, reads, kept, stable⟩

end MicroCFTA.EndpointMemoGateTrace
