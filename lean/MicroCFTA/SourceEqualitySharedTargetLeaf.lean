import MicroCFTA.SourceEqualitySharedTargetForce

/-!
# Native edit leaves with shared class target forcing

Each leaf first forces its class target closure. The native intersection
then uses that stored value and the exact returned state. First forcing
derives construction provenance. Reuse retains the same physical value.
-/
namespace MicroCFTA.SourceEqualitySharedTargetLeaf
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget SourceEqualityClassTarget
open SourceEqualitySharedTargetState SourceEqualitySharedTargetForce
open InternedGuardedLanguage (meaning)

/-- Actual stored target receipts retain every original equality-satisfying selected subterm. -/
theorem _root_.MicroCFTA.SourceEqualitySharedTargetState.Receipt.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values heap path value)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths) (selected : (Term.node symbol terms).atPath path = some part) :
    meaning holds ambient value part := by
  obtain ⟨member, before, after, ready, available, trace, _⟩ := receipt
  exact target_included emptyGuard conjoin clear top record coherent active path member values value trace ready available closed
    holds ambient clearTrue topTrue conjoined symbol terms part accepted satisfied selected

/-- A native edit leaf first forces its shared target, then uses the exact returned native state. -/
inductive Leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) (input : Value Symbol Guard) :
    State width Symbol Guard → Value Symbol Guard → State width Symbol Guard → Prop where
  | apply (forced : Force emptyGuard conjoin clear top record values path before target middle)
      (step : Step emptyGuard conjoin target input middle.native result native) :
      Leaf emptyGuard conjoin clear top record values path input before result (advance middle native)

/-- Actual shared target leaves retain source scope, native validity, and every earlier returned target value. -/
theorem Leaf.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values) (closed : ClosedValues values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = []) :
    Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Retains before after := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known closed member
      have checked := step.verified first.1.native first.2.2.1 (first.2.1.available input available) first.2.2.2.1 inputClosed
        (fun _ _ => true) (fun _ _ _ => rfl)
      exact ⟨first.1.advance _ checked.1 checked.2.1, first.2.1.trans checked.2.1, checked.2.2.1, checked.2.2.2.1,
        first.2.2.2.2.2.trans (advance_retains _ _)⟩

/-- Each actual leaf output is included in its original input language. -/
theorem Leaf.narrows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values) (closed : ClosedValues values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = []) (holds : Guard → Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∀ part, meaning holds ambient result part → meaning holds ambient input part := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known closed member
      have checked := step.verified first.1.native first.2.2.1 (first.2.1.available input available) first.2.2.2.1 inputClosed holds conjoined
      exact fun part accepted => ((checked.2.2.2.2 ambient part).mp accepted).1

/-- Each actual leaf retains an accepted input subterm selected by a satisfied original class. -/
theorem Leaf.keeps_term [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values) (closed : ClosedValues values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = [])
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths) (selected : (Term.node symbol terms).atPath path = some part)
    (inputAccepted : meaning holds ambient input part) : meaning holds ambient result part := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known closed member
      have targetAccepted := (first.1.receipts path _ first.2.2.2.2.1).included coherent active closed holds ambient clearTrue topTrue conjoined
        symbol terms part accepted satisfied selected
      have checked := step.verified first.1.native first.2.2.1 (first.2.1.available input available) first.2.2.2.1 inputClosed holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨inputAccepted, targetAccepted⟩

end MicroCFTA.SourceEqualitySharedTargetLeaf
