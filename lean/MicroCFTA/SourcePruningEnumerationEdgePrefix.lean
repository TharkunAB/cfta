import MicroCFTA.SourcePruningEnumerationShallowChild
import MicroCFTA.SourcePruningEnumerationConstraint

namespace MicroCFTA.SourcePruningEnumerationEdgePrefix
open Fragments EnumerationState EnumerationCorrectness
open InternedConstructorTemplates SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

local instance prefixMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Allocate own equality variables and stage the ordered child actions without running them. -/
noncomputable def prepare (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint) :
    Option (EnumerateM Symbol Constraint
      (Symbol × List (InternedConstructorTemplates.Value Symbol Constraint ×
        List EnumerationState.Suspended ×
        Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint))
 :=
  if arityAllows edge.children.length scs then
    match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => none
    | some (tries, residual) =>
        some (tries.mapM suspend >>= fun own =>
          pure (edge.entry.key.symbol,
            edge.children.zipIdx.map (fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1)), residual))
  else some reject

/-- Pure equality allocations retain every complete realized pending node value. -/
theorem suspended_realized (count : Nat)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationState.State Symbol Constraint) (realized : PendingRealized heap before) :
    PendingRealized heap (suspendedState count before)
 := by
  induction count generalizing before with
  | zero => exact realized
  | succ count ih =>
      apply ih (allocated none before)
      intro slot node scs stored
      change (before.values ++ [.unenumerated none []])[slot]? =
        some (.unenumerated (some node) scs) at stored
      obtain old | fresh := List.mem_append.mp (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact realized oldSlot node scs oldStored
      · simp at fresh

/-- Derive the exact allocation endpoint and the same edge's ordered staged payload. -/
theorem prepare_complete (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationState.State Symbol Constraint) (realized : PendingRealized heap before)
    (aligned : before.counter = before.values.length) :
    if arityAllows edge.children.length scs then
      match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none => prepare scs edge = none
      | some (tries, residual) =>
          let own : List EnumerationState.Suspended := suspendedVars before.counter tries
          let staged := edge.children.zipIdx.map (fun indexed =>
            (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1))
          ∃ action, prepare scs edge = some action ∧
            action before = [.ok ((edge.entry.key.symbol, staged, residual), suspendedState tries.length before)] ∧
            (suspendedState tries.length before).counter = before.counter + tries.length ∧
            (suspendedState tries.length before).counter = (suspendedState tries.length before).values.length ∧
            PendingRealized heap (suspendedState tries.length before)
    else prepare scs edge = some reject
 := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte]
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => simp only [prepare, allowed, ↓reduceIte, projected]
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        dsimp only
        refine ⟨(tries.mapM suspend >>= fun own =>
          pure (edge.entry.key.symbol,
            edge.children.zipIdx.map (fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1)), residual)),
          ?_, ?_, EnumerationSchedule.suspended_counter tries.length before,
          suspended_supply tries.length before aligned, suspended_realized tries.length heap before realized⟩
        · simp only [prepare, allowed, ↓reduceIte, projected]
        · rw [bind_single _ _ before _ _ (suspendMany_exact tries before)]
          rfl
  · simp [allowed, prepare]

end MicroCFTA.SourcePruningEnumerationEdgePrefix
