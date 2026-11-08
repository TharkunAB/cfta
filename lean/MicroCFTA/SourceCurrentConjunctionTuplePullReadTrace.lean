import MicroCFTA.SourceCurrentConjunctionTuplePullReads
import MicroCFTA.SourceCurrentConjunctionTuplePullTotal

/-!
# Actual demand traces of finite and total tuple sampling

The observation records singleton requests in their actual execution order.
It follows the same transitions as the finite sampler. A successful total
sample derives its finite read receipt internally. The receipt supplies no
future operand view or independent exposure schedule.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullReadTrace
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionTuplePull (Cursor Event step start)
open SourceCurrentConjunctionTuplePullAdmission (Status advance drive)
open SourceCurrentConjunctionTuplePullReads (requested Supported)
open SourceCurrentConjunctionCompletionReads (Exposures)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- Every suspended continuation retains the original operand support. -/
def StatusSupported (support : List Node) : Status Symbol Formula → Prop
  | .running cursor _ | .overflow _ cursor => Supported support cursor
  | .fit _ => True

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Record only requests demanded before the observation stops. -/
def demands : Nat → Nat → Nat → Cursor Symbol Formula → List (List Edge) → Physical Symbol Formula → List Node
  | 0, _, _, _, _, _ => []
  | steps + 1, h, budget, cursor, collected, before =>
      (requested cursor).toList ++
        match advance h budget cursor collected before with
        | .done (.running next sampled) after => demands steps h budget next sampled after
        | _ => []

private theorem advance_step (h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before after : Physical Symbol Formula) (status : Status Symbol Formula)
    (actual : advance h budget cursor collected before = .done status after) :
    ∃ event, step h cursor before = .done event after := by
  cases observed : step h cursor before with
  | failed fault middle => simp only [advance, observed, Outcome.bind] at actual; cases actual
  | done event middle =>
      have same : middle = after := by
        cases event with
        | more next | ended =>
            simp only [advance, observed, Outcome.bind] at actual
            exact (Outcome.done.inj actual).2
        | yield tuple next =>
            simp only [advance, observed, Outcome.bind] at actual
            split at actual <;> exact (Outcome.done.inj actual).2
      exact ⟨event, by simp only [same]⟩

private theorem advance_supported (h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before after : Physical Symbol Formula) (status : Status Symbol Formula)
    (support : List Node) (supported : Supported support cursor)
    (actual : advance h budget cursor collected before = .done status after) : StatusSupported support status := by
  cases observed : step h cursor before with
  | failed fault middle => simp only [advance, observed, Outcome.bind] at actual; cases actual
  | done event middle =>
      have smaller := SourceCurrentConjunctionTuplePullProgress.step_next h cursor before middle event observed
      cases event with
      | ended => simp only [advance, observed, Outcome.bind] at actual; cases actual; trivial
      | more next =>
          have continued := SourceCurrentConjunctionTuplePullReads.next_supported support smaller supported
          simp only [advance, observed, Outcome.bind] at actual
          cases actual
          exact continued
      | yield tuple next =>
          have continued := SourceCurrentConjunctionTuplePullReads.next_supported support smaller supported
          simp only [advance, observed, Outcome.bind] at actual
          split at actual <;> cases actual <;> exact continued

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem request_supported (support : List Node) (cursor : Cursor Symbol Formula)
    (supported : Supported support cursor) (node : Node) (member : node ∈ (requested cursor).toList) :
    node ∈ support := by
  cases observed : requested cursor with
  | none => simp only [observed, Option.toList_none, List.not_mem_nil] at member
  | some value =>
      simp only [observed, Option.toList_some, List.mem_singleton] at member
      subst node
      exact SourceCurrentConjunctionTuplePullReads.requested_mem support cursor value supported observed

/-- Every recorded demand belongs to the original operand support, on all outcomes. -/
theorem demands_supported (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula) (support : List Node)
    (supported : Supported support cursor) :
    ∀ node ∈ demands steps h budget cursor collected before, node ∈ support := by
  induction steps generalizing cursor collected before with
  | zero => intro node member; cases member
  | succ steps ih =>
      intro node member
      simp only [demands, List.mem_append] at member
      rcases member with member | member
      · exact request_supported support cursor supported node member
      · cases observed : advance h budget cursor collected before with
        | failed fault after => simp only [observed, List.not_mem_nil] at member
        | done status after =>
            cases status with
            | fit sampled | overflow sampled next => simp only [observed, List.not_mem_nil] at member
            | running next sampled =>
                have continued := advance_supported h budget cursor collected before after (.running next sampled)
                  support supported observed
                simp only [observed] at member
                exact ih next sampled after continued node member

omit [DecidableEq Symbol] in
private theorem exposures_append {first rest : List Node}
    {before middle after : State Symbol Guard} {rows more : List (List Edge)}
    (head : Exposures first before rows middle) (tail : Exposures rest middle more after) :
    Exposures (first ++ rest) before (rows ++ more) after := by
  induction head with
  | nil => exact tail
  | cons own remaining ih => exact .cons own (ih tail)

/-- A successful finite observation derives the exact heap sequence of its actual reads. -/
theorem drive_reads (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before after : Physical Symbol Formula) (status : Status Symbol Formula)
    (actual : drive steps h budget cursor collected before = .done status after) :
    ∃ rows, Exposures (demands steps h budget cursor collected before) before.heap rows after.heap := by
  induction steps generalizing cursor collected before after status with
  | zero => cases actual; exact ⟨[], .nil⟩
  | succ steps ih =>
      cases observed : advance h budget cursor collected before with
      | failed fault middle => simp only [drive, observed, Outcome.bind] at actual; cases actual
      | done reached middle =>
          obtain ⟨event, transition⟩ := advance_step h budget cursor collected before middle reached observed
          obtain ⟨rows, first⟩ := SourceCurrentConjunctionTuplePullReads.step_reads h cursor before middle event transition
          cases reached with
          | fit sampled | overflow sampled next =>
              simp only [drive, observed, Outcome.bind] at actual
              cases actual
              simpa only [demands, observed, List.append_nil] using Exists.intro rows first
          | running next sampled =>
              simp only [drive, observed, Outcome.bind] at actual
              obtain ⟨more, tail⟩ := ih next sampled middle after status actual
              exact ⟨rows ++ more, by simpa only [demands, observed] using exposures_append first tail⟩

/-- A successful total sample supplies its own actual demand graph and original support. -/
theorem sample_reads (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (result : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after) :
    ∃ reads rows, Exposures reads before.heap rows after.heap ∧ ∀ node ∈ reads, node ∈ nodes := by
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have observed := eventual 0
  simp only [Nat.add_zero, actual, SourceCurrentConjunctionTuplePullTotal.observe] at observed
  obtain ⟨rows, receipt⟩ := drive_reads steps h budget (start nodes) [] before after result.toStatus observed
  exact ⟨demands steps h budget (start nodes) [] before, rows, receipt,
    demands_supported steps h budget (start nodes) [] before nodes
      (SourceCurrentConjunctionTuplePullReads.start_supported nodes)⟩

end MicroCFTA.SourceCurrentConjunctionTuplePullReadTrace
