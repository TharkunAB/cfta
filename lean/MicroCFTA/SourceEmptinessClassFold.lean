import MicroCFTA.SourceEmptinessProjection
import MicroCFTA.EqualityReduction
import MicroCFTA.SourceEqualitySelectedRequired

/-!
# Native class requirements in both emptiness folds

The row analysis uses foldr1 order. The refused-class check uses its first
path as the seed of a right fold over the remaining paths. These schedules
retain distinct projection and native request histories. Neither schedule
calls mergeAlternatives. Native leaves use the existing scoped engine; its
word-range and checked-allocation source boundaries remain explicit.
-/
namespace MicroCFTA.SourceEmptinessClassFold
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEmptinessProjection
open InternedGuardedLanguage (meaning)

/-- The closed-operand foldr1 schedule keeps the left projection, tail, and native request in order. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard)) :
    List (List Int) → SourceRecursiveIntersectionThunks.State width Symbol Guard → Value Symbol Guard →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | one (operand : Operand path values before result after) :
      Fold emptyGuard conjoin values [path] before result after
  | cons (operand : Operand path values before value middle)
      (rest : Fold emptyGuard conjoin values (next :: paths) middle tail later)
      (native : Step emptyGuard conjoin value tail later result after) :
      Fold emptyGuard conjoin values (path :: next :: paths) before result after

/-- Every completed fold returns a closed resident result and retains its full constructor history. -/
theorem Fold.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  induction trace with
  | one operand =>
      have checked := operand.effects ready available closed
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | cons operand rest native ih =>
      have first := operand.effects ready available closed
      have remaining := ih first.1 (fun value member => first.2.1.available value (available value member))
      have last := native.verified remaining.1 (remaining.2.1.available _ first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 (fun _ _ => true) (by intro _ _ _; rfl)
      exact ⟨last.1, first.2.1.trans (remaining.2.1.trans last.2.1), last.2.2.1, last.2.2.2.1⟩

/-- Each completed fold retains a common accepted subtree from all of its actual original paths. -/
theorem Fold.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (nonroot : ∀ path ∈ paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    meaning holds ambient result part := by
  induction trace with
  | one operand =>
      exact operand.included ready available closed (nonroot _ (by simp)) holds ambient symbol terms part accepted (selected _ (by simp))
  | cons operand rest native ih =>
      have first := operand.effects ready available closed
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have remaining := rest.effects first.1 tailInputs closed
      have own := operand.included ready available closed (nonroot _ (by simp)) holds ambient symbol terms part accepted (selected _ (by simp))
      have tail := ih first.1 tailInputs
        (fun path member => nonroot path (List.mem_cons_of_mem _ member))
        (fun path member => selected path (List.mem_cons_of_mem _ member))
      have checked := native.verified remaining.1 (remaining.2.1.available _ first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨tail, own⟩

/-- The seeded source fold rotates its seed to the last demanded operand. -/
def seededPaths : List (List Int) → List (List Int)
  | [] => []
  | seed :: rest => rest ++ [seed]

/-- Rotation changes demand order without changing which original paths occur. -/
theorem mem_seededPaths (paths : List (List Int)) (path : List Int) : path ∈ seededPaths paths ↔ path ∈ paths := by
  cases paths <;> simp [seededPaths, or_comm]

/-- The refused-class seeded fold and the analysis fold retain their separate native schedules. -/
def Seeded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (paths : List (List Int)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (result : Value Symbol Guard) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  match paths with
  | [] => result = .empty ∧ after = before
  | seed :: rest => Fold emptyGuard conjoin values (rest ++ [seed]) before result after

/-- The source empty-list fallback returns EmptyNode without changing any state. -/
theorem Seeded.nil [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Seeded emptyGuard conjoin values [] state .empty state := ⟨rfl, rfl⟩

/-- Every completed seeded fold, including its empty-list fallback, retains the same physical invariants. -/
theorem Seeded.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact ⟨ready, pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons => exact Fold.effects trace ready available closed

/-- A completed seeded fold keeps every common selected original subtree. -/
theorem Seeded.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (nonempty : paths ≠ []) (nonroot : ∀ path ∈ paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    meaning holds ambient result part := by
  cases paths with
  | nil => exact False.elim (nonempty rfl)
  | cons seed rest =>
      exact Fold.included trace ready available closed
        (fun path member => nonroot path ((mem_seededPaths (seed :: rest) path).mp member)) holds ambient conjoined symbol terms part accepted
        (fun path member => selected path ((mem_seededPaths (seed :: rest) path).mp member))

/-- A normalized satisfied class supplies a smaller common subtree to the actual analysis fold. -/
theorem class_witness [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    {result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values (paths.map (List.map Int.ofNat)) before result after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (accepted : All₂ (meaning holds ambient) values terms)
    (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, meaning holds ambient result part ∧ part.height < (Term.node symbol terms).height := by
  obtain ⟨first, firstMember, other, otherMember, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstMember, other, otherMember, different⟩
  obtain ⟨part, found⟩ := class_member_exists (.node symbol terms) paths active satisfied first firstMember
  have nonroot := EqualityReduction.class_nonroot paths active (.node symbol terms) satisfied
  refine ⟨part, ?_, ?_⟩
  · have proper : ∀ path ∈ paths.map (List.map Int.ofNat), path ≠ [] := by
      intro path member empty
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact nonroot original present (List.map_eq_nil_iff.mp empty)
    apply trace.included ready available closed proper holds ambient conjoined symbol terms part accepted
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨common, firstFound, otherFound⟩ := class_pair_equal (.node symbol terms) paths active satisfied first original firstMember present
    have same : common = part := Option.some.inj (firstFound.symm.trans found)
    subst common
    simpa only [SourceEqualitySelectedRequired.lookup_natural] using otherFound
  · have bound := atPath_height_bound (.node symbol terms) part first found
    have positive : 0 < first.length := List.length_pos_iff.mpr (nonroot first firstMember)
    omega

end MicroCFTA.SourceEmptinessClassFold
