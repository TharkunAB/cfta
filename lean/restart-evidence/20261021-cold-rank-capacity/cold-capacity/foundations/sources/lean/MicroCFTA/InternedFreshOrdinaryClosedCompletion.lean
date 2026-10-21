import MicroCFTA.InternedFreshOrdinaryRouteLevels
import MicroCFTA.InternedRecordDepthCompletion

/-!
# Repaired closed source construction returns a complete result

The source depth induction derives the decoded heap even for a pending
outcome. The exact pending encounter then supplies two actual source
routes. Their captured suffixes determine equal ordinary choices, which
contradicts the live ordinary mismatch required by that encounter.
-/
namespace MicroCFTA.InternedFreshOrdinaryClosedCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryActiveOrigins InternedFreshOrdinaryActiveReplay
open InternedFreshOrdinaryActiveSite InternedFreshOrdinarySourceHistory
open InternedFreshOrdinaryLevelReplay
open InternedBinderProtocol (Reference NodeKey)

/-- An actual pending site with literal ancestor captures is impossible in a decoded final heap. -/
theorem site_impossible [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) (names : List Reference)
    (inputs : origin.environment = names.map Value.reference) (heap : InternedFreshOrdinaryDepthHeap.Heap final) : False := by
  exact InternedRecordDepthCompletion.site_impossible site heap

/-- Literal source construction in a complete valid decoded cache cannot stop at an unfinished recursive record. -/
theorem literal_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state)
    (key : NodeKey) (final : State Symbol Guard) : build expression (names.map Value.reference) state ≠ .pending key final :=
  InternedRecordDepthCompletion.source_not_pending expression (names.map Value.reference) state context heap covered key final

/-- Every repaired literal-input construction in a complete valid decoded cache returns a complete value and its actual cache. -/
theorem literal_complete [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state) :
    ∃ value final, build expression (names.map Value.reference) state = .done value final := by
  cases result : build expression (names.map Value.reference) state with
  | done value final => exact ⟨value, final, rfl⟩
  | pending key final => exact False.elim (literal_not_pending expression names state context heap covered key final result)

/-- No repaired source expression built from empty captures and caches stops at an unfinished recursive record. -/
theorem closed_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) : build expression [] empty ≠ .pending key final :=
  literal_not_pending expression [] empty InternedFreshOrdinaryContext.empty_context
    InternedFreshOrdinaryDepthHeap.empty_heap empty_correct.2 key final

/-- Every repaired closed source expression returns a complete value and its actual final cache. -/
theorem closed_complete [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value final, build expression [] empty = .done value final :=
  literal_complete expression [] empty InternedFreshOrdinaryContext.empty_context
    InternedFreshOrdinaryDepthHeap.empty_heap empty_correct.2

end MicroCFTA.InternedFreshOrdinaryClosedCompletion
