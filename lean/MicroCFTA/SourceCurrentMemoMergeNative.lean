import MicroCFTA.SourceCurrentMemoMergeComplete
import MicroCFTA.SourceEqualityNativeScoped

/-!
# Completed memo-aware merging in an existing native state

Each call uses the actual constructor heap and completed merge table. Its
returned heap advances the same native state. Both native memo families and
the domain table remain unchanged. This wrapper concerns completed calls.
Lazy publication and runtime forcing remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentMemoMergeNative
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced Origin)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- One completed memo-aware call advances only the constructor heap of the native state. -/
inductive Merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) :
    Value Symbol Guard → Native width Symbol Guard → Memo Symbol Guard →
      Value Symbol Guard → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | done (actual : Call clear top input before.machine.heap memo output heap saved) :
      Merge clear top input before memo output (advanceHeap before heap) saved

/-- Completed calls retain native state and derive all physical result obligations. -/
structure Effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (input : Value Symbol Guard)
    (before : Native width Symbol Guard) (memo : Memo Symbol Guard) (output : Value Symbol Guard)
    (after : Native width Symbol Guard) (saved : Memo Symbol Guard) : Prop where
  ready : IdleReady emptyGuard conjoin after
  keeps : Keeps before.machine.heap after.machine.heap
  costs : CostHeap after.machine.heap
  stored : Stored after.machine.heap saved
  available : Available after.machine.heap output
  closed : input.free = [] → output.free = []
  nodes : after.nodes = before.nodes
  edges : after.edges = before.edges
  domains : after.machine.domains = before.machine.domains
  retained : Extends memo saved

/-- The wrapper retains the literal completed graph and its returned heap. -/
theorem Merge.actual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) :
    ∃ heap, after = advanceHeap before heap ∧ Call clear top input before.machine.heap memo output heap saved := by
  cases trace with
  | done actual => exact ⟨_, rfl, actual⟩

/-- Successful calls preserve idle native tables and derive the physical returned winner. -/
theorem Merge.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Available before.machine.heap input) : Effects emptyGuard conjoin input before memo output after saved := by
  cases trace with
  | done actual =>
      obtain ⟨effect, retained, result, closed⟩ :=
        SourceCurrentMemoMergeEffects.call_effects actual ready.semantic costs stored available
      exact ⟨ready.advance _ effect.keeps effect.semantic, effect.keeps, effect.costs, retained,
        result, closed, rfl, rfl, rfl, actual.extends⟩

/-- A literal present key skips the body and preserves the complete native state. -/
theorem Merge.hit_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) (entry : Entry Symbol Guard)
    (found : memo input.referenceOf = some entry) : after = before ∧ saved = memo ∧ output = entry.result := by
  cases trace with
  | done actual =>
      obtain ⟨sameHeap, sameMemo, returned⟩ := actual.hit_unchanged entry found
      exact ⟨by rw [sameHeap]; rfl, sameMemo, returned⟩

/-- The same completed call retains the independent language and earlier cache coverage. -/
theorem Merge.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (covered : CacheCovers holds ambient memo) (available : Available before.machine.heap input)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true) :
    CacheCovers holds ambient saved ∧ Covers holds ambient input output := by
  cases trace with
  | done actual =>
      obtain ⟨_, _, retained, _, inclusion⟩ := SourceCurrentMemoMergeLanguage.call_language
        clear top holds ambient clearTrue topTrue actual ready.semantic costs stored covered available
      exact ⟨retained, inclusion⟩

/-- One trace supplies physical effects and independent language coverage together. -/
theorem Merge.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (covered : CacheCovers holds ambient memo) (available : Available before.machine.heap input)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true) :
    Effects emptyGuard conjoin input before memo output after saved ∧
      CacheCovers holds ambient saved ∧ Covers holds ambient input output :=
  ⟨trace.effects ready costs stored available, trace.included ready costs stored holds ambient covered available clearTrue topTrue⟩

/-- Existing historical producers remain valid through the actual memo-aware call. -/
theorem Merge.produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) : Produced clear top memo → Produced clear top saved := by
  cases trace with
  | done actual => exact SourceCurrentMemoMergeOrigins.call_produced actual

/-- Warm completed tables admit a finite call inside the existing native state. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (stored : Stored before.machine.heap memo) (covered : CacheCovers holds ambient memo)
    (available : Available before.machine.heap input) :
    ∃ output after saved, Merge clear top input before memo output after saved ∧
      Effects emptyGuard conjoin input before memo output after saved ∧
      CacheCovers holds ambient saved ∧ Covers holds ambient input output := by
  obtain ⟨output, heap, saved, actual, _, _, retained, _, _, _, inclusion⟩ :=
    SourceCurrentMemoMergeComplete.finite clear top holds ambient clearTrue topTrue input before.machine.heap memo
      ready.semantic costs stored covered available
  have trace : Merge clear top input before memo output (advanceHeap before heap) saved := .done actual
  exact ⟨output, _, saved, trace, trace.effects ready costs stored available, retained, inclusion⟩

/-- An empty result table derives finite coverage and an actual stored producer. -/
theorem finite_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : Native width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Available before.machine.heap input) :
    ∃ output after saved, Merge clear top input before empty output after saved ∧
      Effects emptyGuard conjoin input before empty output after saved ∧
      CacheCovers holds ambient saved ∧ Produced clear top saved ∧ Covers holds ambient input output ∧
      ∃ entry, saved input.referenceOf = some entry ∧ entry.original = input ∧ entry.result = output ∧ Origin clear top input output := by
  obtain ⟨output, heap, saved, actual, _, _, covered, produced, _, _, inclusion, entry⟩ :=
    SourceCurrentMemoMergeComplete.cold clear top holds ambient clearTrue topTrue input before.machine.heap ready.semantic costs available
  have trace : Merge clear top input before empty output (advanceHeap before heap) saved := .done actual
  exact ⟨output, _, saved, trace, trace.effects ready costs (SourceCurrentMemoMergeEffects.stored_empty _) available,
    covered, produced, inclusion, entry⟩

end MicroCFTA.SourceCurrentMemoMergeNative

namespace MicroCFTA.SourceCurrentMemoMergeNative
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Native receipts retain the actual completed recursive global reads. -/
inductive Reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) :
    Value Symbol Guard → Native width Symbol Guard → Memo Symbol Guard → Value Symbol Guard →
      Native width Symbol Guard → Memo Symbol Guard → Memos → Memos → Prop where
  | done (receipt : SourceCurrentMemoMergeQueryMemos.CallReads clear top input before.machine.heap memo output heap saved memos final) :
      Reads clear top input before memo output (advanceHeap before heap) saved memos final

/-- A native receipt recovers its actual memo-aware merge wrapper. -/
theorem Reads.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    (receipt : Reads clear top input before memo output after saved memos final) :
    Merge clear top input before memo output after saved := by
  cases receipt with
  | done actual => exact .done actual.graph

/-- Native receipts preserve both original query tables. -/
theorem Reads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    (receipt : Reads clear top input before memo output after saved memos final) : final.query = memos.query := by
  cases receipt with
  | done actual => exact actual.query

/-- The same native call derives coherent final global tables and actual reads. -/
theorem Merge.memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Available before.machine.heap input) (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, Reads clear top input before memo output after saved memos final ∧
      SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final := by
  cases trace with
  | done actual =>
      obtain ⟨final, receipt, effect, _⟩ := SourceCurrentMemoMergeQueryMemos.call_memos
        actual ready.semantic costs stored available memos valid
      exact ⟨final, .done receipt, effect⟩

/-- Physical effects, language coverage, and global receipts use one native call. -/
theorem Merge.verified_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {input output : Value Symbol Guard} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Merge clear top input before memo output after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (covered : CacheCovers holds ambient memo) (available : Available before.machine.heap input)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true) (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, Reads clear top input before memo output after saved memos final ∧
      Effects emptyGuard conjoin input before memo output after saved ∧ CacheCovers holds ambient saved ∧
      Covers holds ambient input output ∧ SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final := by
  obtain ⟨effect, retained, inclusion⟩ := trace.verified ready costs stored holds ambient covered available clearTrue topTrue
  obtain ⟨final, receipt, global⟩ := trace.memos ready costs stored available memos valid
  exact ⟨final, receipt, effect, retained, inclusion, global⟩

local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- Warm source tables have a finite native endpoint with the same actual global reads. -/
theorem source_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (stored : Stored before.machine.heap memo) (covered : CacheCovers holds ambient memo)
    (available : Available before.machine.heap input) (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ output after saved final, Merge clear top input before memo output after saved ∧
      Reads clear top input before memo output after saved memos final ∧
      Effects emptyGuard conjoin input before memo output after saved ∧ CacheCovers holds ambient saved ∧
      Covers holds ambient input output ∧ SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final := by
  obtain ⟨output, after, saved, trace, effect, retained, inclusion⟩ :=
    finite emptyGuard conjoin clear top holds ambient clearTrue topTrue input before memo ready costs stored covered available
  obtain ⟨final, receipt, global⟩ := trace.memos ready costs stored available memos valid
  exact ⟨output, after, saved, final, trace, receipt, effect, retained, inclusion, global⟩

/-- Empty source result tables derive native effects, coverage, producers, and all global receipts. -/
theorem source_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (input : Value Symbol Guard) (before : Native width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Available before.machine.heap input) (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ output after saved final, Merge clear top input before empty output after saved ∧
      Reads clear top input before empty output after saved memos final ∧
      Effects emptyGuard conjoin input before empty output after saved ∧ CacheCovers holds ambient saved ∧
      Produced clear top saved ∧ Covers holds ambient input output ∧
      SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final ∧
      ∃ entry, saved input.referenceOf = some entry ∧ entry.original = input ∧ entry.result = output ∧ Origin clear top input output := by
  obtain ⟨output, after, saved, trace, effect, covered, produced, inclusion, entry⟩ :=
    finite_cold emptyGuard conjoin clear top holds ambient clearTrue topTrue input before ready costs available
  obtain ⟨final, receipt, global⟩ := trace.memos ready costs (SourceCurrentMemoMergeEffects.stored_empty _) available memos valid
  exact ⟨output, after, saved, final, trace, receipt, effect, covered, produced, inclusion, global, entry⟩

end MicroCFTA.SourceCurrentMemoMergeNative
