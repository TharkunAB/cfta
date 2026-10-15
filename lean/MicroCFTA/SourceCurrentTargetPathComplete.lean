import MicroCFTA.SourceEqualityProjectionPathComplete
import MicroCFTA.SourceEqualitySharedTargetWorkerProofs

/-!
# Shared target completion from selected path domains

Each captured operand needs only its selected projection domain. General
merging and native intersection receive the closed projected values.
Unselected ordinary siblings can remain open. Actual demand-prefix word
checks and all existing target graphs remain unchanged.
-/
namespace MicroCFTA.SourceEqualityTargetOperand
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open InternedGuardedLanguage (meaning)

/-- A selected operand derives closed output without closing unrelated captured children. -/
theorem Operand.path_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domain : ForestClosed path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | force projection merged =>
      have projected := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      have middleReady := ready.advance _ projected.1 projected.2.1
      have checked := merged.effects middleReady projected.2.2.1 projected.2.2.2
      exact ⟨checked.1, projected.1.trans checked.2.1, checked.2.2.1, checked.2.2.2.1,
        checked.2.2.2.2.1, checked.2.2.2.2.2.1, checked.2.2.2.2.2.2⟩

/-- A proper-path operand retains the accepted original subterm in its selected path domain. -/
theorem Operand.path_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domain : ForestClosed path values) (nonroot : path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  cases path with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases trace with
      | force projection merged =>
          have projected := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
          exact merged.included (ready.advance _ projected.1 projected.2.1) projected.2.2.1 projected.2.2.2
            holds ambient clearTrue topTrue part
            (SourceEqualityProjectionPathDomain.forest_included projection ready.semantic available domain
              holds ambient symbol terms part accepted selected)

end MicroCFTA.SourceEqualityTargetOperand

namespace MicroCFTA.SourceCurrentTargetPathComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityProjectionPathDomain

/-- A selected captured path completes projection and merging in its existing full native state. -/
theorem operand_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (path : List Int) (values : List (Value Symbol Guard)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (domain : ForestClosed path values) :
    ∃ result after, Operand clear top path values before result after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  obtain ⟨projected, heap, projection, checked⟩ := SourceEqualityProjectionPathComplete.forest_complete path values
    before.machine.heap ready.semantic available domain
  obtain ⟨result, after, merged, _⟩ := SourceEqualityNativeMerge.complete emptyGuard conjoin clear top projected
    (advanceHeap before heap) (ready.advance heap checked.1 checked.2.1) checked.2.2.1 checked.2.2.2
  have trace : Operand clear top path values before result after := .force projection merged
  exact ⟨result, after, trace, trace.path_effects ready available domain⟩

end MicroCFTA.SourceCurrentTargetPathComplete

namespace MicroCFTA.SourceEqualityDemandTarget
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityProjectionPathDomain

/-- Actual target folds derive closed operands from each selected path domain. -/
theorem Fold.path_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  induction trace with
  | nil seedDemand =>
      have checked := seedDemand.path_effects ready available (domains _ List.mem_cons_self)
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | @cons path before value middle paths tail later result after operand rest step ih =>
      have first := operand.path_effects ready available (domains path (by simp))
      have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact domains _ List.mem_cons_self
        · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have remaining := ih first.1 (fun value member => first.2.1.available value (available value member)) tailDomains
      have checked := step.verified remaining.1 (remaining.2.1.available value first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 (fun _ _ => true) (fun _ _ _ => rfl)
      exact ⟨checked.1, first.2.1.trans (remaining.2.1.trans checked.2.1), checked.2.2.1, checked.2.2.2.1⟩

/-- A completed target needs closedness only at its captured projection paths. -/
theorem Target.path_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  cases trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons fold => exact fold.path_effects ready available domains

end MicroCFTA.SourceEqualityDemandTarget

namespace MicroCFTA.SourceCurrentTargetPathComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityTargetOperand SourceEqualityProjectionPathDomain
open SourceEqualityDemandTarget SourceEqualityDemandTargetComplete

/-- Each finite source fold completes from local path domains and its actual-prefix native word checks. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin before)
    (ranges : FoldRanges emptyGuard conjoin clear top values seed paths before) (available : Values before.machine.heap values)
    (domains : ∀ path ∈ seed :: paths, ForestClosed path values) :
    ∃ result after, Fold emptyGuard conjoin clear top values seed paths before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  induction paths generalizing before with
  | nil =>
      obtain ⟨result, after, operand, finalReady, keeps, resultAvailable, resultClosed, _⟩ :=
        operand_complete emptyGuard conjoin clear top seed values before ready available (domains _ List.mem_cons_self)
      exact ⟨result, after, .nil operand, finalReady, keeps, resultAvailable, resultClosed⟩
  | cons path paths ih =>
      cases ranges with
      | cons restPlan stepPlan =>
          obtain ⟨value, middle, operand, middleReady, firstKeeps, valueAvailable, valueClosed, _⟩ :=
            operand_complete emptyGuard conjoin clear top path values before ready available (domains path (by simp))
          have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
            intro own member
            rcases List.mem_cons.mp member with rfl | member
            · exact domains _ List.mem_cons_self
            · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
          obtain ⟨tail, later, rest, laterReady, restKeeps, tailAvailable, tailClosed⟩ :=
            ih middle middleReady (restPlan value middle operand)
              (fun value member => firstKeeps.available value (available value member)) tailDomains
          obtain ⟨result, after, step, finalReady, stepKeeps, resultAvailable, resultClosed, _⟩ :=
            SourceEqualityNativeScoped.complete emptyGuard conjoin later laterReady value tail
              (restKeeps.available value valueAvailable) tailAvailable valueClosed tailClosed
              (stepPlan value middle operand tail later rest) (fun _ _ => true) (fun _ _ _ => rfl)
          exact ⟨result, after, .cons operand rest step, finalReady,
            firstKeeps.trans (restKeeps.trans stepKeeps), resultAvailable, resultClosed⟩

/-- Path-local projection domains derive stable finite execution of the literal target worker. -/
theorem target_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (ranges : TargetRanges emptyGuard conjoin clear top values paths before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values) :
    ∃ result after, Target emptyGuard conjoin clear top values paths before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      SourceEqualityDemandTargetWorkerComplete.StableRun
        (fun p h c n => SourceEqualityDemandTargetWorker.target emptyGuard conjoin clear top p h c n values paths before) result after := by
  have completed : ∃ result after, Target emptyGuard conjoin clear top values paths before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
    cases paths with
    | nil => exact ⟨.empty, before, .nil, ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
    | cons seed paths =>
        obtain ⟨result, after, fold, checked⟩ := fold_complete emptyGuard conjoin clear top values seed paths before ready ranges available domains
        exact ⟨result, after, .cons fold, checked⟩
  obtain ⟨result, after, trace, ready, keeps, available, closed⟩ := completed
  exact ⟨result, after, trace, ready, keeps, available, closed, SourceEqualityDemandTargetWorkerComplete.target_stable trace⟩

end MicroCFTA.SourceCurrentTargetPathComplete

namespace MicroCFTA.SourceEqualityDemandTarget
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open InternedGuardedLanguage (meaning)

/-- An actual fold retains every common selected original subterm in its operand path domains. -/
theorem Fold.path_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values)
    (nonroot : ∀ path ∈ seed :: paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ seed :: paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  induction trace with
  | nil seedDemand =>
      exact seedDemand.path_included ready available (domains _ List.mem_cons_self) (nonroot _ List.mem_cons_self)
        holds ambient clearTrue topTrue symbol terms part accepted (selected _ List.mem_cons_self)
  | @cons path before value middle paths tail later result after operand rest step ih =>
      have first := operand.path_effects ready available (domains path (by simp))
      have tailInputs : Values middle.machine.heap values := fun value member => first.2.1.available value (available value member)
      have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact domains _ List.mem_cons_self
        · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailNonroot : ∀ own ∈ seed :: paths, own ≠ [] := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact nonroot _ List.mem_cons_self
        · exact nonroot own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailSelected : ∀ own ∈ seed :: paths, SymbolicSignedPaths.lookup (.node symbol terms) own = some part := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact selected _ List.mem_cons_self
        · exact selected own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailAccepted := ih first.1 tailInputs tailDomains tailNonroot tailSelected
      have ownAccepted := operand.path_included ready available (domains path (by simp)) (nonroot path (by simp))
        holds ambient clearTrue topTrue symbol terms part accepted (selected path (by simp))
      have remaining := rest.path_effects first.1 tailInputs tailDomains
      have checked := step.verified remaining.1 (remaining.2.1.available value first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨tailAccepted, ownAccepted⟩

/-- Every nonempty target retains a common selected subterm without closing unrelated siblings. -/
theorem Target.path_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (nonempty : paths ≠ []) (nonroot : ∀ path ∈ paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  cases trace with
  | nil => exact False.elim (nonempty rfl)
  | cons fold => exact fold.path_included ready available domains nonroot holds ambient clearTrue topTrue conjoined symbol terms part accepted selected

end MicroCFTA.SourceEqualityDemandTarget

namespace MicroCFTA.SourceCurrentTargetPathComplete
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeScoped SourceEqualityDemandTarget SourceEqualityClassTarget SourceEqualityProjectionPathDomain
open EqualityNormalize
open InternedGuardedLanguage (meaning)

/-- Every other-path operand inherits its selected path domain from the captured class. -/
theorem operand_domains (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (selected : Path) :
    ∀ path ∈ operandPaths record.paths selected, ForestClosed path values := by
  intro path member
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
  exact domains original (List.mem_filter.mp originalIn).1

/-- A current class target retains its original equality-satisfying subterm from local path domains. -/
theorem class_target_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard)) (target : Value Symbol Guard)
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before target after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : ClassSat (.node symbol terms) record.paths) (selected : (Term.node symbol terms).atPath path = some part) :
    meaning holds ambient target part := by
  apply trace.path_included ready available (operand_domains record values domains path)
    (operandPaths_nonempty record.paths active path) (operandPaths_nonroot record coherent active path)
    holds ambient clearTrue topTrue conjoined symbol terms part accepted
  intro other included
  change other ∈ (EqualityNarrowing.others record.paths path).map (List.map Int.ofNat) at included
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp included
  obtain ⟨common, selectedAt, otherAt⟩ := class_pair_equal (.node symbol terms) record.paths active satisfied path original member
    (List.mem_filter.mp originalIn).1
  have samePart := Option.some.inj (selectedAt.symm.trans selected)
  subst common
  simpa only [SourceEqualitySelectedRequired.lookup_natural] using otherAt

end MicroCFTA.SourceCurrentTargetPathComplete

namespace MicroCFTA.SourceEqualitySharedTargetState
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget SourceEqualityClassTarget SourceEqualityProjectionPathDomain
open InternedGuardedLanguage (meaning)

/-- Actual stored receipts derive closed availability from the selected class paths alone. -/
theorem Receipt.available_path [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values heap path value)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    Available heap value ∧ value.free = [] := by
  obtain ⟨_, first, final, ready, available, trace, retained⟩ := receipt
  have checked := trace.path_effects ready available (SourceCurrentTargetPathComplete.operand_domains record values domains path)
  exact ⟨retained.available value checked.2.2.1, checked.2.2.2⟩

/-- A stored actual receipt retains each equality-satisfying selected subterm in the local path domains. -/
theorem Receipt.included_path [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : Receipt width emptyGuard conjoin clear top record values heap path value)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths) (selected : (Term.node symbol terms).atPath path = some part) :
    meaning holds ambient value part := by
  obtain ⟨member, before, after, ready, available, trace, _⟩ := receipt
  exact SourceCurrentTargetPathComplete.class_target_included emptyGuard conjoin clear top record coherent active path member values value
    trace ready available domains holds ambient clearTrue topTrue conjoined symbol terms part accepted satisfied selected

/-- First forcing stores its actual target and preserves all earlier receipts under local path domains. -/
theorem Ready.store_path [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {before : State width Symbol Guard} (ready : Ready emptyGuard conjoin clear top record values base before)
    (known : Values base values) (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (value : Value Symbol Guard) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before.native value after) :
    Ready emptyGuard conjoin clear top record values base (SourceEqualitySharedTargetState.store before path value after) := by
  have available : Values before.native.machine.heap values := fun value member => ready.captured.available value (known value member)
  have checked := trace.path_effects ready.native available (SourceCurrentTargetPathComplete.operand_domains record values domains path)
  refine ⟨checked.1, ready.captured.trans checked.2.1, ?_⟩
  intro other target present
  by_cases same : other = path
  · subst other
    have equal : value = target := by simpa only [SourceEqualitySharedTargetState.store, Cache.put, ite_true, Option.some.injEq] using present
    subst target
    exact ⟨member, before.native, after, ready.native, available, trace, pure_keeps _ checked.1.semantic.ready⟩
  · have original : before.targets other = some target := by simpa only [SourceEqualitySharedTargetState.store, Cache.put, same, ite_false] using present
    exact (ready.receipts other target original).grows checked.2.1

end MicroCFTA.SourceEqualitySharedTargetState

namespace MicroCFTA.SourceEqualitySharedTargetForce
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget SourceEqualityClassTarget SourceEqualityProjectionPathDomain
open SourceEqualitySharedTargetState

/-- First forcing and reuse need only the captured class projection domains. -/
theorem Force.path_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (member : path ∈ record.paths) :
    Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ after.targets path = some value ∧ Retains before after := by
  cases trace with
  | hit present =>
      have available := (ready.receipts path value present).available_path domains
      exact ⟨ready, pure_keeps _ ready.native.semantic.ready, available.1, available.2, present, fun _ _ stored => stored⟩
  | miss absent actual =>
      have available : Values before.native.machine.heap values := fun value member => ready.captured.available value (known value member)
      have checked := actual.path_effects ready.native available (SourceCurrentTargetPathComplete.operand_domains record values domains path)
      refine ⟨ready.store_path known domains path member value _ actual, checked.2.1, checked.2.2.1, checked.2.2.2, ?_, ?_⟩
      · simp only [SourceEqualitySharedTargetState.store, Cache.put, ite_true]
      · intro other target present
        by_cases same : other = path
        · subst other; rw [absent] at present; cases present
        · simpa only [SourceEqualitySharedTargetState.store, Cache.put, same, ite_false] using present

end MicroCFTA.SourceEqualitySharedTargetForce

namespace MicroCFTA.SourceCurrentTargetPathComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassTarget SourceEqualityProjectionPathDomain
open SourceEqualitySharedTargetState SourceEqualitySharedTargetForce

/-- Class-local selected path domains and actual first-force ranges derive a stable completed force. -/
theorem force_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
    (known : Values base values) (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (before : State width Symbol Guard) (ready : Ready emptyGuard conjoin clear top record values base before)
    (ranges : ForceRanges emptyGuard conjoin clear top record values path before) :
    ∃ value after, Force emptyGuard conjoin clear top record values path before value after ∧
      Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ after.targets path = some value ∧ Retains before after ∧
      SourceEqualitySharedTargetWorkerProofs.StableRun
        (fun p h c n => SourceEqualitySharedTargetWorker.force emptyGuard conjoin clear top p h c n record values path before) value after := by
  have completed : ∃ value after, Force emptyGuard conjoin clear top record values path before value after := by
    cases present : before.targets path with
    | some value => exact ⟨value, before, .hit present⟩
    | none =>
        have actualRanges := ranges
        simp only [ForceRanges, present] at actualRanges
        obtain ⟨value, native, actual, _⟩ := target_complete emptyGuard conjoin clear top values
          (operandPaths record.paths path) before.native ready.native actualRanges
          (fun value member => ready.captured.available value (known value member)) (operand_domains record values domains path)
        exact ⟨value, SourceEqualitySharedTargetState.store before path value native, .miss present actual⟩
  obtain ⟨value, after, trace⟩ := completed
  obtain ⟨ready, kept, available, closed, stored, retained⟩ := trace.path_effects ready known domains member
  exact ⟨value, after, trace, ready, kept, available, closed, stored, retained,
    SourceEqualitySharedTargetWorkerProofs.force_stable emptyGuard conjoin clear top record values trace⟩

end MicroCFTA.SourceCurrentTargetPathComplete

