import MicroCFTA.SourceCurrentConjunctionWorklist

/-!
# Completed conjunction emptiness decisions

An open input returns false before any constructor read. A closed input
completes its dynamic allocated worklist and the literal Boolean fixed
point. The finite grow counter bounds comparisons, not runtime work.
The graph retains the chosen resident read schedule. It does not identify
that schedule with lazy GHC forcing or pending memo publication.
-/
namespace MicroCFTA.SourceCurrentConjunctionDecision
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (Run closed)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)

/-- The current body has an open shortcut or an actual allocated closed worklist. -/
inductive Decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (budget : Nat) (start : Value Symbol Guard) : Physical → Bool → Physical → Prop where
  | open_input (openInput : closed start = false) : Decision budget start before false before
  | closed (closedInput : closed start = true)
      (explored : Run budget [] [[start]] before table after)
      (grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table (budget + 1)
        (fun _ => false) = some known) :
      Decision budget start before (SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start) after

/-- Initial physical invariants derive an actual finite decision and its returned states. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (budget : Nat) (start : Value Symbol Guard) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    ∃ result after, Decision budget start before result after ∧ Effects before after := by
  cases admitted : closed start with
  | false => exact ⟨false, before, .open_input admitted, Effects.refl before ready⟩
  | true =>
      obtain ⟨table, after, explored, effects, _, bound⟩ := SourceCurrentConjunctionWorklist.entered budget [[start]] before ready
        (by intro nodes member value included; cases List.mem_singleton.mp member; cases List.mem_singleton.mp included; exact available)
      have grown := SourceCurrentConjunctionEmptinessTable.grow_rounds_complete .empty key closed table budget 0
        (by simpa using bound)
      exact ⟨_, after, .closed admitted explored grown, effects⟩

/-- An open source decision preserves both initial physical states exactly. -/
theorem open_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {result : Bool}
    (actual : Decision budget start before result after) (openInput : closed start = false) : result = false ∧ after = before := by
  cases actual with
  | open_input _ => exact ⟨rfl, rfl⟩
  | closed same _ _ => rw [same] at openInput; cases openInput

end MicroCFTA.SourceCurrentConjunctionDecision
