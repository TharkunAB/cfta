import MicroCFTA.SourceEmptinessTaskExposureWitness
import MicroCFTA.SourceEmptinessTaskBodies

/-!
# Accepted rows of actual final exploration entries

Each new entry receives its accepted row witness at its actual exposure.
Reached task effects preserve normalized fields and captured bodies. These
effects transport each witness to the actual final state. No final accepted
row or class-language oracle is assumed. The proof uses complete row reads
and the existing scoped native state. Runtime demand correspondence remains
a separate obligation.
-/
namespace MicroCFTA.SourceEmptinessTaskEntryRows
open Language EqualityNormalize InternedConstructorTemplates
open SourceEmptinessTasks SourceEmptinessTaskRows SourceEmptinessTaskBodies
open SourceEmptinessTaskTrace (Run)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Row" => ConservativeEmptinessRows.Row (Value Symbol Guard)
local notation "Entry" => DelayedEmptinessExplore.Entry (Task Symbol Guard) (Value Symbol Guard)
local notation "TaskState" => SourceEmptinessTasks.State
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Acceptance of the original stored value selects its retained row and original class bodies. -/
def AcceptedRows (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (state : TaskState width Symbol Guard) (entry : Entry) : Prop :=
  ∀ term, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient entry.value term →
    ∃ (sourceRow : Row) (taskRow : List (Task Symbol Guard)), taskRow ∈ entry.rows ∧
      RowBodyReceipt state sourceRow taskRow ∧ Active sourceRow.classes ∧ Satisfies term sourceRow.classes ∧
      ∃ symbol terms, term = .node symbol terms ∧
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) sourceRow.children terms

/-- A final entry retains its actual earlier exposure and the body effects of its continuation. -/
def Exposed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : TaskState width Symbol Guard) (entry : Entry) : Prop :=
  ∃ before after, Expose entry.value before entry.rows after ∧ Ready top conjoin before ∧
    FieldHeap before.native.machine.heap ∧ RetainsBodies after state

/-- Physical body retention preserves accepted-row witnesses without changing original row occurrences. -/
theorem AcceptedRows.transport
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {ambient : InternedGuardedLanguage.Env Symbol} {before after : TaskState width Symbol Guard} {entry : Entry}
    (accepted : AcceptedRows formulas solver ambient before entry) (retained : RetainsBodies before after) :
    AcceptedRows formulas solver ambient after entry := by
  intro term inputAccepted
  obtain ⟨sourceRow, taskRow, member, receipt, active, satisfied, shape⟩ := accepted term inputAccepted
  exact ⟨sourceRow, taskRow, member, receipt.transport retained, active, satisfied, shape⟩

/-- Actual normalized exposure derives each accepted row before the reached continuation runs. -/
theorem exposure [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (entry : Entry)
    {before after : TaskState width Symbol Guard} (trace : Expose entry.value before entry.rows after)
    (ready : Ready top conjoin before) (fields : FieldHeap before.native.machine.heap) :
    AcceptedRows formulas solver ambient after entry := by
  intro term inputAccepted
  obtain ⟨sourceRow, taskRow, member, receipt, active, satisfied, shape⟩ :=
    SourceEmptinessTaskExposureWitness.accepted trace ready fields formulas solver ambient term inputAccepted
  exact ⟨sourceRow, taskRow, member, rowReceipt_body receipt, active, satisfied, shape⟩

/-- Every newly stored lookup derives its actual exposure and final accepted-row body witnesses. -/
theorem new_entry [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (trace : Run (width := width) top conjoin budget seen pending before final after) :
    Ready top conjoin before → FieldHeap before.native.machine.heap →
      ∀ key entry, DelayedEmptinessExplore.lookup key final = some entry →
        DelayedEmptinessExplore.lookup key seen = some entry ∨
          (Exposed after entry ∧ AcceptedRows formulas solver ambient after entry) := by
  induction trace with
  | done => intro ready fields key entry found; exact Or.inl found
  | empty forced encoded rest ih =>
      intro ready fields key entry found
      exact ih (forced.effects ready).1 (SourceEmptinessTaskFields.force_fields forced ready fields) key entry found
  | skipped forced encoded skipped rest ih =>
      intro ready fields key entry found
      exact ih (forced.effects ready).1 (SourceEmptinessTaskFields.force_fields forced ready fields) key entry found
  | @admit task before value forcedHeap identity closed budget seen rows exposedHeap pending final after
      forced encoded fresh exposed rest ih =>
      intro ready fields key entry found
      have first := forced.effects ready
      have firstFields := SourceEmptinessTaskFields.force_fields forced ready fields
      have captured := exposed.effects first.1
      have capturedFields := SourceEmptinessTaskFields.expose_fields exposed first.1 firstFields
      rcases ih captured.1 capturedFields key entry found with old | entered
      · by_cases same : key = identity
        · subst key
          have identical : (⟨identity, value, rows⟩ : Entry) = entry := by
            simpa only [DelayedEmptinessExplore.lookup, ↓reduceIte, Option.some.injEq] using old
          subst entry
          have retained := run_bodies rest captured.1
          exact Or.inr ⟨⟨forcedHeap, exposedHeap, exposed, first.1, firstFields, retained⟩,
            (exposure formulas solver ambient ⟨identity, value, rows⟩ exposed first.1 firstFields).transport retained⟩
        · exact Or.inl (by simpa only [DelayedEmptinessExplore.lookup, same, ↓reduceIte] using old)
      · exact Or.inr entered

/-- Empty-start execution derives final accepted-row witnesses for every actual stored entry. -/
theorem entry [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (trace : Run (width := width) top conjoin budget [] pending before final after)
    (ready : Ready top conjoin before) (fields : FieldHeap before.native.machine.heap)
    (key : Int) (stored : Entry) (found : DelayedEmptinessExplore.lookup key final = some stored) :
    Exposed after stored ∧ AcceptedRows formulas solver ambient after stored := by
  rcases new_entry formulas solver ambient trace ready fields key stored found with impossible | actual
  · cases impossible
  · exact actual

end MicroCFTA.SourceEmptinessTaskEntryRows
