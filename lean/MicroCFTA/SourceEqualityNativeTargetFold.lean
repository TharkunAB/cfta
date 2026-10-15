import MicroCFTA.SourceEqualityNativeScoped

/-!
# Actual native equality-target intersection lists

The source takes the first operand as seed and folds the remaining operands
from right to left. Every step uses the returned native state of its tail.
Word-range premises refer only to the actual completed tail graphs.
-/
namespace MicroCFTA.SourceEqualityNativeTargetFold
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open InternedGuardedLanguage (meaning)

/-- The actual first-seeded source right fold, with full native state at each step. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (seed : Value Symbol Guard) :
    List (Value Symbol Guard) → SourceRecursiveIntersectionThunks.State width Symbol Guard →
      Value Symbol Guard → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | nil : Fold emptyGuard conjoin seed [] state seed state
  | cons (rest : Fold emptyGuard conjoin seed values before tail middle)
      (step : Step emptyGuard conjoin value tail middle result after) :
      Fold emptyGuard conjoin seed (value :: values) before result after

/-- The empty source list returns EmptyNode; a nonempty list uses its first operand as seed. -/
inductive IntersectList [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    List (Value Symbol Guard) → SourceRecursiveIntersectionThunks.State width Symbol Guard →
      Value Symbol Guard → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | nil : IntersectList emptyGuard conjoin [] state .empty state
  | cons (fold : Fold emptyGuard conjoin seed values before result after) :
      IntersectList emptyGuard conjoin (seed :: values) before result after

/-- A finite source intersection is false on the empty operand list. -/
def ListMeaning (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (values : List (Value Symbol Guard)) (term : Term Symbol) : Prop :=
  values ≠ [] ∧ ∀ value ∈ values, meaning holds ambient value term

/-- Completed folds derive actual warm state and the exact conjunction of all operands. -/
theorem Fold.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {seed result : Value Symbol Guard}
    {values : List (Value Symbol Guard)} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin seed values before result after) (ready : IdleReady emptyGuard conjoin before)
    (seedAvailable : Available before.machine.heap seed) (available : Values before.machine.heap values)
    (seedClosed : seed.free = []) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, meaning holds ambient result term ↔
        meaning holds ambient seed term ∧ ∀ value ∈ values, meaning holds ambient value term := by
  induction trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, seedAvailable, seedClosed, by simp⟩
  | @cons values before tail middle value result after rest step ih =>
      have tailFacts := ih ready seedAvailable (fun value member => available value (List.mem_cons_of_mem _ member))
        (fun value member => closed value (List.mem_cons_of_mem _ member))
      have stepFacts := step.verified tailFacts.1 (tailFacts.2.1.available value (available value List.mem_cons_self))
        tailFacts.2.2.1 (closed value List.mem_cons_self) tailFacts.2.2.2.1 holds conjoined
      refine ⟨stepFacts.1, tailFacts.2.1.trans stepFacts.2.1, stepFacts.2.2.1, stepFacts.2.2.2.1, ?_⟩
      intro ambient term
      rw [stepFacts.2.2.2.2 ambient term, tailFacts.2.2.2.2 ambient term]
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨seedAccepted, restAccepted⟩, firstAccepted⟩
        exact ⟨seedAccepted, firstAccepted, restAccepted⟩
      · rintro ⟨seedAccepted, firstAccepted, restAccepted⟩
        exact ⟨⟨seedAccepted, restAccepted⟩, firstAccepted⟩

/-- Actual completed target lists retain idle memos, both histories, and exact nonempty intersection language. -/
theorem IntersectList.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {result : Value Symbol Guard}
    {values : List (Value Symbol Guard)} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : IntersectList emptyGuard conjoin values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      ∀ ambient term, meaning holds ambient result term ↔ ListMeaning holds ambient values term := by
  cases trace with
  | nil =>
      refine ⟨ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl, ?_⟩
      intro ambient term
      simp [meaning, ListMeaning]
  | cons fold =>
      have checked := fold.verified ready (available _ List.mem_cons_self)
        (fun value member => available value (List.mem_cons_of_mem _ member)) (closed _ List.mem_cons_self)
        (fun value member => closed value (List.mem_cons_of_mem _ member)) holds conjoined
      refine ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, ?_⟩
      intro ambient term
      simpa only [ListMeaning, List.cons_ne_nil, ne_eq, not_false_eq_true, true_and,
        List.mem_cons, forall_eq_or_imp] using checked.2.2.2.2 ambient term

/-- Word checks for a finite fold refer to each actual completed tail, not arbitrary cache extensions. -/
inductive FoldRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (seed : Value Symbol Guard) :
    List (Value Symbol Guard) → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | nil : FoldRanges emptyGuard conjoin seed [] state
  | cons (rest : FoldRanges emptyGuard conjoin seed values before)
      (ranges : ∀ tail middle, Fold emptyGuard conjoin seed values before tail middle →
        SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
          (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) middle) :
      FoldRanges emptyGuard conjoin seed (value :: values) before

/-- Finite target folds complete from actual prefix word checks and local native progress. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (seed : Value Symbol Guard)
    (values : List (Value Symbol Guard)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : FoldRanges emptyGuard conjoin seed values before) (ready : IdleReady emptyGuard conjoin before)
    (seedAvailable : Available before.machine.heap seed) (available : Values before.machine.heap values)
    (seedClosed : seed.free = []) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ result after, Fold emptyGuard conjoin seed values before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  induction ranges with
  | nil => exact ⟨seed, _, .nil, ready, pure_keeps _ ready.semantic.ready, seedAvailable, seedClosed⟩
  | @cons values before value rest ranges ih =>
      obtain ⟨tail, middle, tailTrace, tailReady, tailKeeps, tailAvailable, tailClosed⟩ := ih ready seedAvailable
        (fun value member => available value (List.mem_cons_of_mem _ member))
        (fun value member => closed value (List.mem_cons_of_mem _ member))
      obtain ⟨result, after, step, finalReady, keeps, resultAvailable, resultClosed, _⟩ := SourceEqualityNativeScoped.complete
        emptyGuard conjoin middle tailReady value tail (tailKeeps.available value (available value List.mem_cons_self))
        tailAvailable (closed value List.mem_cons_self) tailClosed (ranges tail middle tailTrace) holds conjoined
      exact ⟨result, after, .cons tailTrace step, finalReady, tailKeeps.trans keeps, resultAvailable, resultClosed⟩

/-- Source intersection-list range checks keep the empty and first-seeded branches separate. -/
def ListRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  match values with
  | [] => True
  | seed :: rest => FoldRanges emptyGuard conjoin seed rest state

/-- Every finite actual source target list completes while retaining all warm native tables. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ranges : ListRanges emptyGuard conjoin values before)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ result after, IntersectList emptyGuard conjoin values before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  cases values with
  | nil => exact ⟨.empty, before, .nil, ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons seed rest =>
      obtain ⟨result, after, trace, checked⟩ := fold_complete emptyGuard conjoin seed rest before ranges ready
        (available _ List.mem_cons_self) (fun value member => available value (List.mem_cons_of_mem _ member))
        (closed _ List.mem_cons_self) (fun value member => closed value (List.mem_cons_of_mem _ member)) holds conjoined
      exact ⟨result, after, .cons trace, checked⟩

end MicroCFTA.SourceEqualityNativeTargetFold
