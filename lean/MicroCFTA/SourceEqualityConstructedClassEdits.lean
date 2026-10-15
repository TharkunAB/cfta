import MicroCFTA.SourceEqualityClassTargetAPI
import MicroCFTA.SourceEqualityNativeClassEdits

/-!
# Constructed physical targets through native class edits

Each captured target has an actual demanded construction receipt and a
retained history into the edit base. These receipts derive target scope
and no loss of equality-satisfying terms. Shared forcing remains separate.
-/
namespace MicroCFTA.SourceEqualityConstructedClassEdits
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget
open SourceEqualityClassTarget SourceEqualityNativeEditGraph
open EqualityNormalize
open InternedGuardedLanguage (meaning)

/-- Every captured class target has a literal construction receipt whose actual cache grows into the edit base. -/
structure Constructed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (target : Path → Value Symbol Guard) : Prop where
  actual : ∀ path ∈ record.paths, ∃ before after : NativeState width Symbol Guard,
    IdleReady emptyGuard conjoin before ∧ Values before.machine.heap values ∧
      Target emptyGuard conjoin clear top values (operandPaths record.paths path) before (target path) after ∧ Keeps after.machine.heap base

/-- Actual construction receipts derive closed target availability at the common retained edit base. -/
theorem Constructed.known [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {target : Path → Value Symbol Guard} (constructed : Constructed width emptyGuard conjoin clear top record values base target) (closed : ClosedValues values) :
    ∀ path ∈ record.paths, Available base (target path) ∧ (target path).free = [] := by
  intro path member
  obtain ⟨before, after, ready, available, trace, retained⟩ := constructed.actual path member
  have checked := trace.effects ready available closed
  exact ⟨retained.available _ checked.2.2.1, checked.2.2.2⟩

/-- Constructed physical class targets retain every original equality-satisfying selected subterm. -/
theorem Constructed.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {target : Path → Value Symbol Guard} (constructed : Constructed width emptyGuard conjoin clear top record values base target)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (accepted : All₂ (meaning holds ambient) values terms) (satisfied : ClassSat (.node symbol terms) record.paths) :
    ∀ path ∈ record.paths, ∀ part, (Term.node symbol terms).atPath path = some part → meaning holds ambient (target path) part := by
  intro path member part selected
  obtain ⟨before, after, ready, available, trace, retained⟩ := constructed.actual path member
  exact target_included emptyGuard conjoin clear top record coherent active path member values (target path) trace ready available closed
    holds ambient clearTrue topTrue conjoined symbol terms part accepted satisfied selected

/-- Actual native class edits with constructed targets preserve exactly the accepted terms that already satisfy the class. -/
theorem class_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard) (target : Path → Value Symbol Guard)
    (constructed : Constructed width emptyGuard conjoin clear top record values base target)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    {before results after} (trace : EditList (width := width) emptyGuard conjoin (SourceEqualityEdits.build (SourceEqualityClassEdits.edits record.paths target)) values before results after)
    (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (symbol : Symbol) (terms : List (Term Symbol)) (satisfied : ClassSat (.node symbol terms) record.paths) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms := by
  have exact := SourceEqualityNativeClassEdits.class_exact emptyGuard conjoin base holds ambient conjoined record coherent active target
    (constructed.known closed) trace retained ready available closed symbol terms
  constructor
  · exact fun accepted => (exact.mp accepted).1
  · intro accepted
    exact exact.mpr ⟨accepted, constructed.included coherent active closed holds ambient clearTrue topTrue conjoined symbol terms accepted satisfied⟩

/-- Constructed target scope and actual-prefix native checks derive finite stable class edits with no loss of class-satisfying terms. -/
theorem class_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard) (target : Path → Value Symbol Guard)
    (constructed : Constructed width emptyGuard conjoin clear top record values base target)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (before : NativeState width Symbol Guard) (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (ranges : SourceEqualityNativeEditRanges.ListRanges emptyGuard conjoin (SourceEqualityEdits.build (SourceEqualityClassEdits.edits record.paths target)) values before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, EditList emptyGuard conjoin (SourceEqualityEdits.build (SourceEqualityClassEdits.edits record.paths target)) values before results after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      SourceEqualityNativeEditWorkerComplete.StableRun
        (fun fuel head native => SourceEqualityNativeEditWorker.editAll emptyGuard conjoin fuel head native (SourceEqualityClassEdits.edits record.paths target) values before) results after ∧
      ∀ symbol terms, ClassSat (.node symbol terms) record.paths →
        (All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms) := by
  obtain ⟨results, after, trace, finalReady, keeps, resident, resultClosed, stable, _⟩ := SourceEqualityNativeClassEdits.class_complete
    emptyGuard conjoin base holds ambient conjoined record coherent active target (constructed.known closed) values before retained ready ranges available closed
  exact ⟨results, after, trace, finalReady, keeps, resident, resultClosed, stable,
    fun symbol terms satisfied => class_exact emptyGuard conjoin clear top record coherent active values base target constructed holds ambient
      clearTrue topTrue conjoined trace retained ready available closed symbol terms satisfied⟩

end MicroCFTA.SourceEqualityConstructedClassEdits
