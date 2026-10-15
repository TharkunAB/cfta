import MicroCFTA.SourceCurrentMemoSharedTargetForce

/-!
# Shared target leaves with the actual completed merge table

Each leaf first forces its captured class target. The native intersection
then uses that value at the returned native state. Native execution retains
the completed merge table and all returned target slots. Only the original
selected path domains must be closed. Other original siblings can be open.
-/
namespace MicroCFTA.SourceCurrentMemoSharedTargetLeaf
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetForce
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced)
open InternedGuardedLanguage (meaning)

/-- A leaf forces its shared target before the actual native intersection. -/
inductive Leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (input : Value Symbol Guard) :
    State width Symbol Guard → Value Symbol Guard → State width Symbol Guard → Prop where
  | apply (forced : Force emptyGuard conjoin clear top record values path before target middle)
      (step : Step emptyGuard conjoin target input middle.native result native) :
      Leaf emptyGuard conjoin clear top record values path input before result (advance middle native)

/-- Actual leaves retain native readiness, costs, stored entries, and returned slots. -/
theorem Leaf.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = []) :
    Ready emptyGuard conjoin clear top record values base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Retains before after := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known domains member
      have own := first.2.1.available input available
      have checked := step.verified first.1.native first.2.2.1 own first.2.2.2.1 inputClosed
        (fun _ _ => true) (fun _ _ _ => rfl)
      have costs := step.cost_heap first.1.native first.1.costs first.2.2.1 own
      exact ⟨first.1.advance _ checked.1 checked.2.1 costs, first.2.1.trans checked.2.1,
        checked.2.2.1, checked.2.2.2.1, first.2.2.2.2.2.trans (advance_retains _ _)⟩

/-- Native execution retains the exact merge table returned by target forcing. -/
theorem Leaf.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after) :
    Extends before.memo after.memo := by
  cases trace with
  | apply forced _ => exact forced.extends

/-- Actual leaves retain the historical producers of every completed merge entry. -/
theorem Leaf.produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after) :
    Produced clear top before.memo → Produced clear top after.memo := by
  cases trace with
  | apply forced _ => exact forced.produced

/-- Independent cache coverage follows actual target forcing and remains unchanged by the native step. -/
theorem Leaf.covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (member : path ∈ record.paths)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (covered : CacheCovers holds ambient before.memo)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    CacheCovers holds ambient after.memo := by
  cases trace with
  | apply forced _ => exact forced.covered ready known domains member holds ambient covered clearTrue topTrue conjoined

/-- Every actual leaf output is included in the language of its concrete input. -/
theorem Leaf.narrows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∀ part, meaning holds ambient result part → meaning holds ambient input part := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known domains member
      have checked := step.verified first.1.native first.2.2.1 (first.2.1.available input available)
        first.2.2.2.1 inputClosed holds conjoined
      exact fun part accepted => ((checked.2.2.2.2 ambient part).mp accepted).1

/-- Actual leaves retain accepted input subterms selected by the satisfied captured class. -/
theorem Leaf.keeps_term [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = [])
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (covered : CacheCovers holds ambient before.memo)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths)
    (selected : (Term.node symbol terms).atPath path = some part)
    (inputAccepted : meaning holds ambient input part) : meaning holds ambient result part := by
  cases trace with
  | apply forced step =>
      have first := forced.effects ready known domains member
      have currentCovered := forced.covered ready known domains member holds ambient covered clearTrue topTrue conjoined
      have targetAccepted := (first.1.receipts path _ first.2.2.2.2.1).included coherent active
        holds ambient currentCovered clearTrue topTrue conjoined symbol terms part accepted satisfied selected
      have checked := step.verified first.1.native first.2.2.1 (first.2.1.available input available)
        first.2.2.2.1 inputClosed holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨inputAccepted, targetAccepted⟩

/-- Word checks occur only at the native state returned by the actual target force. -/
structure LeafRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (input : Value Symbol Guard) (before : State width Symbol Guard) : Prop where
  force : ForceRanges emptyGuard conjoin clear top record values path before
  step : ∀ target middle, Force emptyGuard conjoin clear top record values path before target middle →
    SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) middle.native

/-- Actual first-force ranges and returned-state word checks derive finite leaves. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
    (before : State width Symbol Guard) (ready : Ready emptyGuard conjoin clear top record values base before)
    (ranges : LeafRanges emptyGuard conjoin clear top record values path input before)
    (available : Available before.native.machine.heap input) (inputClosed : input.free = []) :
    ∃ result after, Leaf emptyGuard conjoin clear top record values path input before result after ∧
      Ready emptyGuard conjoin clear top record values base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ Retains before after := by
  obtain ⟨target, middle, forced, middleReady, keeps, targetAvailable, targetClosed, _⟩ :=
    SourceCurrentMemoSharedTargetForce.complete emptyGuard conjoin clear top record values base known domains
      path member before ready ranges.force
  obtain ⟨result, native, step, _⟩ := SourceEqualityNativeScoped.complete emptyGuard conjoin middle.native middleReady.native
    target input targetAvailable (keeps.available input available) targetClosed inputClosed (ranges.step target middle forced)
    (fun _ _ => true) (fun _ _ _ => rfl)
  have trace : Leaf emptyGuard conjoin clear top record values path input before result (advance middle native) := .apply forced step
  exact ⟨result, _, trace, trace.effects ready known domains member available inputClosed⟩

end MicroCFTA.SourceCurrentMemoSharedTargetLeaf
