import MicroCFTA.SourceEqualitySelectedNativeScope

/-!
# Actual selected and required paths through the native class fold

Original physical records stay aligned with actual source gate queries.
Required paths run on the original forest. The selected class fold starts
at their actual returned heap in the retained full native state. One final
literal empty propagation completes this live source branch.
-/
namespace MicroCFTA.SourceEqualitySelectedClassFold
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open InternedSourceClassSelection (Query selected)
open InternedGuardedLanguage (meaning)

/-- Literal selected/required receipts precede the selected physical class fold and final propagation. -/
structure Execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (queries : List (Query Symbol Guard)) (middle : InternedConstructorTemplates.State Symbol Guard)
    (required : List (Value Symbol Guard)) (heap : InternedConstructorTemplates.State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) : Prop where
  stages : SourceEqualitySelectedRequired.Execution unconstrained values (records.map SourceEqualityClassOrder.Record.paths) before.machine.heap queries middle required heap
  narrowed : Pass emptyGuard conjoin clear top (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap before heap) results after

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
variable {records : List SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {before : NativeState width Symbol Guard}
variable {queries : List (Query Symbol Guard)} {middle : InternedConstructorTemplates.State Symbol Guard}
variable {required : List (Value Symbol Guard)} {heap : InternedConstructorTemplates.State Symbol Guard} {results : List (Value Symbol Guard)} {after : NativeState width Symbol Guard}

/-- Complete actual stages derive idle warm native scope, both cache histories, and closed final outputs. -/
theorem Execution.effects (trace : Execution unconstrained emptyGuard conjoin clear top records values before queries middle required heap results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  have first := SourceEqualitySelectedNativeScope.effects trace.stages ready available closed
  have last := SourceEqualityClassFoldEffects.pass_effects trace.narrowed first.2.1 first.2.2.1 first.2.2.2
  exact ⟨last.1, first.1.trans last.2.1, last.2.2⟩

/-- The selected live branch narrows its original forest and retains every term satisfying its selected classes. -/
theorem Execution.language (trace : Execution unconstrained emptyGuard conjoin clear top records values before queries middle required heap results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      ((∀ record ∈ SourceEqualitySelectedRecords.keep records queries, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
        All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  have keptCoherent := SourceEqualitySelectedRecords.coherent records queries coherent
  have keptActive := SourceEqualitySelectedRecords.active records queries active
  have first := SourceEqualitySelectedRequired.narrow_keep trace.stages ready.semantic available closed holds ambient symbol terms
  have scope := SourceEqualitySelectedNativeScope.effects trace.stages ready available closed
  have last := SourceEqualityClassFoldLanguage.pass_language emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined trace.narrowed
    keptCoherent keptActive scope.2.1 scope.2.2.1 scope.2.2.2 symbol terms
  refine ⟨fun accepted => first.1 (last.1 accepted), ?_⟩
  intro satisfied accepted
  apply last.2 satisfied
  apply first.2 accepted
  intro path member
  obtain ⟨paths, included, selectedPath⟩ := List.mem_flatten.mp member
  have physical : paths ∈ (SourceEqualitySelectedRecords.keep records queries).map SourceEqualityClassOrder.Record.paths := by
    rw [SourceEqualitySelectedRecords.trace_paths trace.stages.selection]
    exact included
  obtain ⟨record, member, same⟩ := List.mem_map.mp physical
  rw [← same] at selectedPath
  exact EqualityNormalize.class_member_exists (.node symbol terms) record.paths (keptActive record member) (satisfied record member) path selectedPath

/-- When all original class constraints hold, the selected live branch preserves exact original forest membership. -/
theorem Execution.exact_when_satisfied (trace : Execution unconstrained emptyGuard conjoin clear top records values before queries middle required heap results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : EqualityNormalize.Satisfies (.node symbol terms) (records.map SourceEqualityClassOrder.Record.paths)) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms := by
  have bounds := trace.language coherent active ready available closed holds ambient clearTrue topTrue conjoined symbol terms
  refine ⟨bounds.1, bounds.2 ?_⟩
  intro record member
  exact satisfied record.paths (List.mem_map.mpr ⟨record, (SourceEqualitySelectedRecords.sublist records queries).subset member, rfl⟩)

/-- Actual prefix checks derive complete finite selected native narrowing without supplying a completed fold. -/
theorem after_prefix (stages : SourceEqualitySelectedRequired.Execution unconstrained values (records.map SourceEqualityClassOrder.Record.paths)
      before.machine.heap queries middle required heap)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (ranges : Ranges emptyGuard conjoin clear top (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap before heap)) :
    ∃ results after, Execution unconstrained emptyGuard conjoin clear top records values before queries middle required heap results after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      SourceEqualityClassFoldWorkerProofs.StableRun
        (fun e p h c n => SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n
          (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap before heap)) results after := by
  have scope := SourceEqualitySelectedNativeScope.effects stages ready available closed
  obtain ⟨results, after, narrowed, finalReady, keeps, resident, resultClosed, stable⟩ :=
    SourceEqualityClassFoldAPI.complete emptyGuard conjoin clear top _ required (advanceHeap before heap) ranges scope.2.1 scope.2.2.1 scope.2.2.2
  exact ⟨results, after, ⟨stages, narrowed⟩, finalReady, scope.1.trans keeps, resident, resultClosed, stable⟩

end MicroCFTA.SourceEqualitySelectedClassFold
