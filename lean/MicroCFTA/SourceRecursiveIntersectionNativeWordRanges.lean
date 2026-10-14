import MicroCFTA.SourceRecursiveIntersectionCompileNodeBounds
import MicroCFTA.SourceRecursiveIntersectionNativeCorrectness

/-!
# Checked word ranges on actual finite native prefixes

The resource premise checks each memoized request reached by finite native
execution. It assumes no completed result or sufficient execution bound.
Actual prefixes and appended continuations retain the same word checks.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Check the existing source word bounds at the current native request instruction. -/
def Words (width : Nat) (code : Code Symbol Guard A) : Prop :=
  match code with
  | .node request _ => ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right
  | .edge request _ => SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right
  | _ => True

/-- Every actual finite yielded prefix retains checked request words, without a completion premise. -/
def WordRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  ∀ fuel next after, Steps emptyGuard conjoin fuel code state next after → Words width next

/-- The zero-length actual prefix gives the current request's word check. -/
theorem WordRanges.current [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : WordRanges emptyGuard conjoin code state) : Words width code := ranges 0 code state (.refl _ _)

/-- An actual yielded prefix retains the resource premise for its exact remaining code and state. -/
theorem WordRanges.after_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : WordRanges emptyGuard conjoin code state) (fuel : Nat) (trace : Steps emptyGuard conjoin fuel code state next after) :
    WordRanges emptyGuard conjoin next after := by
  intro extra final current rest
  exact ranges _ final current (Steps.trans emptyGuard conjoin fuel extra code next final state after current trace rest)

/-- One actual yielded native step retains every later word check. -/
theorem WordRanges.after_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : WordRanges emptyGuard conjoin code state) (one : step emptyGuard conjoin code state = .yielded next after) :
    WordRanges emptyGuard conjoin next after :=
  ranges.after_trace emptyGuard conjoin code next state after 1 (.cons _ _ _ _ _ _ 0 one (.refl _ _))

/-- Appending code does not change the request words at a non-returning source instruction. -/
theorem words_before_bind (width : Nat) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (checked : Words width (code.bind next)) : Words width code := by
  cases code <;> first | exact checked | trivial

/-- Word checks of an appended execution include every actual prefix of its original source body. -/
theorem WordRanges.before_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : WordRanges emptyGuard conjoin (code.bind next) state) : WordRanges emptyGuard conjoin code state := by
  intro fuel current after trace
  exact words_before_bind width current next (ranges fuel (current.bind next) after
    (Steps.bind emptyGuard conjoin fuel code current state after trace next))

/-- A completed original body retains resource checks at its actual appended continuation. -/
theorem WordRanges.after_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : WordRanges emptyGuard conjoin (code.bind next) state) (value : A)
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after) : WordRanges emptyGuard conjoin (next value) after := by
  obtain ⟨fuel, trace⟩ := evaluated.trace
  have appended := Steps.bind emptyGuard conjoin fuel code (.pure value) state after trace next
  exact ranges.after_trace emptyGuard conjoin (code.bind next) (next value) state after fuel appended

end MicroCFTA.SourceRecursiveIntersectionNative
