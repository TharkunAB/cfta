import MicroCFTA.SourceRecursiveIntersectionNativeCapacity
import MicroCFTA.SourceRecursiveIntersectionNativePrefixSplit

/-!
# Capacity checks on actual finite native prefixes

The resource condition bounds only counters in actual reached caches.
It assumes no request provenance, completed result, or sufficient fuel.
Exact traces retain the condition through bodies and outer continuations.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNativeCapacity
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionNative

/-- Every actual yielded prefix stays within the three source cache supplies. -/
def CacheRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard) : Prop :=
  ∀ fuel next after, Steps emptyGuard conjoin fuel code state next after → Capacity bits after.machine

/-- The empty actual prefix checks the initial cache. -/
theorem CacheRanges.current [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (ranges : CacheRanges bits emptyGuard conjoin code state) : Capacity bits state.machine := ranges 0 code state (.refl _ _)

/-- A reached cache and its actual remaining code retain all later capacity checks. -/
theorem CacheRanges.after_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (ranges : CacheRanges bits emptyGuard conjoin code state) (fuel : Nat)
    (trace : Steps emptyGuard conjoin fuel code state next after) : CacheRanges bits emptyGuard conjoin next after := by
  intro extra final current later
  exact ranges _ final current (Steps.trans emptyGuard conjoin fuel extra code next final state after current trace later)

/-- One actual native step retains the remaining cache-capacity contract. -/
theorem CacheRanges.after_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (ranges : CacheRanges bits emptyGuard conjoin code state)
    (one : step emptyGuard conjoin code state = .yielded next after) : CacheRanges bits emptyGuard conjoin next after :=
  ranges.after_trace bits emptyGuard conjoin code next state after 1 (.cons _ _ _ _ _ _ 0 one (.refl _ _))

/-- Every actual prefix of an inner body is an actual prefix of its appended source computation. -/
theorem CacheRanges.before_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (ranges : CacheRanges bits emptyGuard conjoin (code.bind next) state) : CacheRanges bits emptyGuard conjoin code state := by
  intro fuel current after trace
  exact ranges fuel (current.bind next) after (Steps.bind emptyGuard conjoin fuel code current state after trace next)

/-- A completed actual inner body retains capacity checks at its exact outer continuation. -/
theorem CacheRanges.after_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state after : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (ranges : CacheRanges bits emptyGuard conjoin (code.bind next) state) (fuel : Nat) (value : A)
    (trace : Steps emptyGuard conjoin fuel code state (.pure value) after) : CacheRanges bits emptyGuard conjoin (next value) after :=
  ranges.after_trace bits emptyGuard conjoin _ _ _ _ fuel (Steps.bind emptyGuard conjoin fuel code (.pure value) state after trace next)

/-- Appending a continuation retains the current word check until the body returns. -/
theorem words_bind_nonpure [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (nonpure : ∀ value, code ≠ .pure value) (checked : Words width code) : Words width (code.bind next) := by
  cases code with
  | pure value => exact False.elim (nonpure value rfl)
  | _ => exact checked

/-- Word checks on every prefix no longer than an actual complete body cover every actual body prefix. -/
theorem wordRanges_of_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (code : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (complete : Steps emptyGuard conjoin fuel code state (.pure value) after)
    (checked : ∀ extra next final, extra ≤ fuel → Steps emptyGuard conjoin extra code state next final → Words width next) :
    WordRanges emptyGuard conjoin code state := by
  intro extra next final trace
  exact checked extra next final (complete.length_le_complete trace) trace

end MicroCFTA.SourceRecursiveIntersectionNativeCapacity
