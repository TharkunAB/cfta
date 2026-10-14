import MicroCFTA.SourceRecursiveIntersectionNativeWordRanges

/-!
# Completed range certificates from actual finite-prefix word checks

Actual resource checks derive every checked request in a completed nested
evaluation. The resource premise assumes no successful execution. Existing
completed-run correctness can use the derived certificate.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual finite-prefix word checks derive the complete request certificate of any resulting evaluation. -/
theorem Evaluation.bounds_of_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {code : Code Symbol Guard A} {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : A}
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after) :
    WordRanges emptyGuard conjoin code state → Bounds evaluated := by
  induction evaluated with
  | pure => intro ranges; exact .pure _ _
  | work tail ih =>
      intro ranges
      exact .work (ih (ranges.after_step emptyGuard conjoin _ _ _ _ rfl))
  | enter tail ih =>
      intro ranges
      exact .enter (ih (ranges.after_step emptyGuard conjoin _ _ _ _ rfl))
  | read tail ih =>
      intro ranges
      exact .read (ih (ranges.after_step emptyGuard conjoin _ _ _ _ rfl))
  | optionalBinder done tail ih =>
      intro ranges
      exact .optionalBinder done (ih (ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, done])))
  | @nodeDirect A request actual next state chosen middle final value result lookup body tail bodyIH tailIH =>
      intro ranges
      have entered : WordRanges emptyGuard conjoin ((compileNode actual).bind next) chosen :=
        ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup])
      have bodyRanges := entered.before_bind emptyGuard conjoin (compileNode actual) next chosen
      have tailRanges := entered.after_body emptyGuard conjoin (compileNode actual) next chosen middle value body
      exact .nodeDirect lookup (bodyIH bodyRanges) (tailIH tailRanges)
  | @nodeReady A request next state chosen current final handle value result lookup demand tail ih =>
      intro ranges
      obtain ⟨key, requested, _, _⟩ := lookupNode_memoized request state chosen handle lookup
      have checked := ranges.current emptyGuard conjoin (.node request next) state
      have safe := checked key requested
      have tailRanges : WordRanges emptyGuard conjoin (next value) current :=
        ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup, demand])
      exact .nodeReady lookup demand safe (ih tailRanges)
  | @edgeReady A request next state chosen current final handle value result lookup demand tail ih =>
      intro ranges
      have safe := ranges.current emptyGuard conjoin (.edge request next) state
      have tailRanges : WordRanges emptyGuard conjoin (next value) current :=
        ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup, demand])
      exact .edgeReady lookup demand safe (ih tailRanges)
  | @nodeStarted A request actual next state chosen current middle final handle value result lookup demand body tail bodyIH tailIH =>
      intro ranges
      obtain ⟨key, requested, _, _⟩ := lookupNode_memoized request state chosen handle lookup
      have checked := ranges.current emptyGuard conjoin (.node request next) state
      have safe := checked key requested
      have entered : WordRanges emptyGuard conjoin ((compileNode actual).bind fun value => .finishNode handle value (next value)) current :=
        ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup, demand])
      have bodyRanges := entered.before_bind emptyGuard conjoin (compileNode actual) (fun value => .finishNode handle value (next value)) current
      have frameRanges := entered.after_body emptyGuard conjoin (compileNode actual) (fun value => .finishNode handle value (next value)) current middle value body
      have tailRanges : WordRanges emptyGuard conjoin (next value) (SourceRecursiveIntersectionThunks.finishNode handle value middle) :=
        frameRanges.after_step emptyGuard conjoin _ _ _ _ rfl
      exact .nodeStarted lookup demand safe (bodyIH bodyRanges) (tailIH tailRanges)
  | @edgeStarted A request actual next state chosen current middle final handle value result lookup demand body tail bodyIH tailIH =>
      intro ranges
      have safe := ranges.current emptyGuard conjoin (.edge request next) state
      have entered : WordRanges emptyGuard conjoin ((compileEdge emptyGuard conjoin actual).bind fun value => .finishEdge handle value (next value)) current :=
        ranges.after_step emptyGuard conjoin _ _ _ _ (by simp only [step, lookup, demand])
      have bodyRanges := entered.before_bind emptyGuard conjoin (compileEdge emptyGuard conjoin actual) (fun value => .finishEdge handle value (next value)) current
      have frameRanges := entered.after_body emptyGuard conjoin (compileEdge emptyGuard conjoin actual) (fun value => .finishEdge handle value (next value)) current middle value body
      have tailRanges : WordRanges emptyGuard conjoin (next value) (SourceRecursiveIntersectionThunks.finishEdge handle value middle) :=
        frameRanges.after_step emptyGuard conjoin _ _ _ _ rfl
      exact .edgeStarted lookup demand safe (bodyIH bodyRanges) (tailIH tailRanges)
  | finishNode tail ih =>
      intro ranges
      exact .finishNode (ih (ranges.after_step emptyGuard conjoin _ _ _ _ rfl))
  | finishEdge tail ih =>
      intro ranges
      exact .finishEdge (ih (ranges.after_step emptyGuard conjoin _ _ _ _ rfl))

end MicroCFTA.SourceRecursiveIntersectionNative
