import MicroCFTA.SourceCurrentClassHistoryEntry

open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityOriginalAllocationHistory
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "prefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "operations" => SourceEqualityConstraintMemoAllocation.initial

#print axioms SourceCurrentClassHistoryEntry.constructed
#print axioms SourceCurrentClassHistoryEntry.entry
#print axioms SourceCurrentClassHistoryEntry.cold_scan_memos
#print axioms SourceCurrentClassHistoryEntry.cold_scan_sound
#check @SourceCurrentClassHistoryEntry.constructed
#check @SourceCurrentClassHistoryEntry.entry
#check @SourceCurrentClassHistoryEntry.cold_scan_memos
#check @SourceCurrentClassHistoryEntry.cold_scan_sound

namespace MicroCFTA.ClassHistoryKernelProbe

private def cache : Cache.State Key := Cache.emptyState
private def topResult := SourceEqualityConstraintAllocation.intern (some []) cache
private def topCache : Cache.State Key := topResult.2
private theorem topDone : SourceEqualityConstraintAllocation.construct (top).equalities cache =
    (.ok (.live 0 []), topCache) := rfl
private theorem topHistory : History cache topCache [top] := by
  exact History.construct (.start cache) SourceEqualityConstraintConstructors.top_cached topDone

-- One actual constructor retains a live empty field and its exact issued identity.
example : SourceEqualityConstraintAllocation.construct (top).equalities cache =
    (.ok (.live 0 []), topCache) := topDone
example : topCache.next = 1 := rfl
example : topCache.table (SourceEqualityPartialConstraintKey.key []) = some ⟨0, []⟩ := by cbv
example : SourceEqualityConstraintMemoAllocation.Valid (operations topCache) := topHistory.operations_valid Cache.empty_valid
example : (operations topCache).constraints = topCache := rfl
example : ∃ loaded : Allocated,
    SourceEqualityConstraintFieldLookup.load top topCache = .ok (some loaded) ∧
    SourceEqualityConjoinAllocation.readback loaded = top ∧
    SourceEqualityConstraintAllocation.Ready topCache loaded.stored ∧
    SourceEqualityPhysicalPayload.read (top).equalities = .ok loaded.stored.payload :=
  SourceEqualityOriginalFieldOrigins.Origin.load top topCache SourceEqualityConstraintConstructors.top_cached
    ((topHistory.verified Cache.empty_valid).2.2 top (by simp))

-- The empty-prefix guard returns before combination and retains the entire operation state.
example : prefix (.live 0 []) (top).guard (.live 0 []) (operations topCache) =
    (.ok .unchanged, operations topCache) := rfl

private def contradiction : Guard := ⟨none, .top⟩
private theorem contradictionHistory : History cache cache [contradiction] := by
  exact History.construct (.start cache) (by intro classes impossible; cases impossible) rfl
example : SourceEqualityConstraintMemoAllocation.Valid (operations cache) := contradictionHistory.operations_valid Cache.empty_valid
example : SourceEqualityConstraintFieldLookup.load contradiction cache =
    .ok (some (⟨.contradiction, .top⟩ : Allocated)) := rfl
example : prefix .contradiction contradiction.guard .contradiction (operations cache) =
    (.ok .emptyChildren, operations topCache) := rfl

section Entry
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Empty syntax uses the empty covered history and its literal constructor equation.
example (width : Nat) :
    SourceEqualityConstraintMemoAllocation.Valid (operations cache) ∧
    SourceEqualityNativeScoped.IdleReady top SourceEqualityPCSNativeEdge.conjoin
      (SourceEqualityNativeInitial.cold width (InternedConstructorTemplates.empty : InternedConstructorTemplates.State Symbol Guard)) := by
  have checked := SourceCurrentClassHistoryEntry.constructed width (History.start cache) Cache.empty_valid
    (.empty : InternedNestedConstruction.Syntax Symbol Guard)
    (by intro original member; cases member) .empty InternedConstructorTemplates.empty
    (by simp only [InternedFreshOrdinaryConstruction.build])
  exact ⟨checked.1, checked.2.1⟩

-- The public entry derives a complete actual prefix, rather than taking a chosen branch as an input.
example (width : Nat)
    {initialCache finalCache : Cache.State Key} {originals : List Guard}
    (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (inherited : Stored) (inheritedReady : SourceEqualityConstraintAllocation.Ready finalCache inherited) :
    ∃ loaded : Allocated, ∃ branch,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      (prefix loaded.stored loaded.guard inherited (operations finalCache)).1 = .ok branch ∧
      SourceEqualityPhysicalClassEntry.entry edge.entry.key.constraint inherited.payload = .ok branch ∧
      SourceEqualityConstraintMemoAllocation.Valid (prefix loaded.stored loaded.guard inherited (operations finalCache)).2 ∧
      SourceEqualityConstraintMemoAllocation.Grows (operations finalCache)
        (prefix loaded.stored loaded.guard inherited (operations finalCache)).2 := by
  obtain ⟨loaded, found, _, _, complete⟩ := SourceCurrentClassHistoryEntry.entry
    width history valid expression covered value heap built edge resident
  obtain ⟨branch, done, checked, finalValid, growth⟩ := complete inherited inheritedReady
  exact ⟨loaded, branch, found, done, checked, finalValid, growth⟩

-- Duplicate constructor occurrences do not impose a distinct-field premise on entry.
example (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ [top, top]) :
    InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression := by
  have twice : History cache topCache [top, top] :=
    History.construct topHistory SourceEqualityConstraintConstructors.top_cached (by cbv)
  exact twice.syntax_valid expression covered

end Entry
end MicroCFTA.ClassHistoryKernelProbe
