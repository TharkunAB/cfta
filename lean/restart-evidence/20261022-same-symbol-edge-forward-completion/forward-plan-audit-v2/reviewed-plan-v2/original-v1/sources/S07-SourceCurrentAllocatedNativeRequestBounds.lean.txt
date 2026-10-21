import MicroCFTA.SourceRecursiveIntersectionCodeBounds
import MicroCFTA.SourceEqualityNativeDemandOperations
import MicroCFTA.SourceEqualityNativeDemandTrace

/-!
# Strict request bounds in actual checked edge bodies

The independent original-input schedule supplies the decreasing measure.
Checked rejection emits no child request. Acceptance emits only the original
ordered child pairs. Word plans inspect actual checked yielded prefixes.
These bounds do not assert general checked completion or recursive meaning.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRequestBounds
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Each actual accepted child pair strictly decreases the independent original edge request bound. -/
theorem child_below [DecidableEq Symbol] (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (scope : EdgeScope source request) (complete : Completes (view source holds)
      (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (arity : request.left.children.length = request.right.children.length)
    (pair : Value Symbol Guard × Value Symbol Guard) (member : pair ∈ request.left.children.zip request.right.children) :
    NodeBelow source holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete)
      ⟨request.domain, pair.1, pair.2⟩ := by
  refine ⟨scope.child source facts request pair member, ?_⟩
  apply immediate_requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) _ complete
  apply Immediate.edge (SourceRecursiveIntersectionSchedule.domain request.domain.key) (row holds request.left) (row holds request.right)
    (inputOf pair.1, inputOf pair.2)
  · simpa only [row, List.length_map] using arity
  · change (inputOf pair.1, inputOf pair.2) ∈
      (request.left.children.map inputOf).zip (request.right.children.map inputOf)
    rw [List.zip_map]
    exact List.mem_map.mpr ⟨pair, member, rfl⟩

/-- Accepted child code derives its bound from original pairs, for its actual allocated annotation. -/
theorem children_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (scope : EdgeScope source request) (complete : Completes (view source holds)
      (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : EdgeReady state request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (arity : request.left.children.length = request.right.children.length) :
    Below source holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete)
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state := by
  let bound := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  have stable : Stable input := by
    intro before after growth pair known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have inputs : ∀ pair ∈ request.left.children.zip request.right.children, input state pair := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 inside.1,
      valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 inside.2⟩
  have calls : ∀ pair ∈ request.left.children.zip request.right.children, ∀ current,
      SourceRecursiveIntersectionKernel.Valid current → input current pair →
        Safe (requestNode request.domain pair.1 pair.2) current (fun after value => Available after.heap value) := by
    intro pair _ current _ known
    exact safe_requestNode request.domain pair.1 pair.2 current known
  have built := safe_walk (fun pair => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) input _ stable available_stable calls state valid inputs
  have bounded := below_walk source holds bound (fun pair => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) input _ stable available_stable calls
    (fun pair member current _ _ => below_requestNode source holds bound _ current
      (child_below source facts holds request scope complete arity pair member)) state valid inputs
  exact below_bind source holds bound _ _ state valid _ built bounded
    (fun values after _ _ _ => below_work source holds bound _ after)

/-- A rejected or mismatched source sentinel has no recursive request at any body bound. -/
theorem sentinel_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (left : EdgeValue Symbol Guard) (state : Machine Symbol Guard) :
    Below source holds bound (SourceEqualityNativeCheckedCode.sentinel left) state :=
  below_work source holds bound _ state

/-- An actual yielded checked prefix derives its next source bound without assuming any child completion. -/
theorem body_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (scope : EdgeScope source request) (complete : Completes (view source holds)
      (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (before : State width) (code : Code Symbol Guard (EdgeValue Symbol Guard)) (after : State width)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine) (ready : EdgeReady before.native.machine request)
    (yielded : body request .pure before = .yielded (.code code) after) :
    Below source holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete)
      code after.native.machine := by
  have same : after.native = before.native := by
    simpa only [yielded, Outcome.state] using SourceEqualityNativeDemandOperations.body_native request .pure before
  rw [same]
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [sentinel, code_bind_pure] at yielded
    cases yielded
    exact sentinel_below source holds _ _ _
  · rename_i equalArity
    have arity : request.left.children.length = request.right.children.length := by omega
    split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [sentinel, code_bind_pure] at yielded
          cases yielded
          exact sentinel_below source holds _ _ _
        · simp only [sentinel, code_bind_pure] at yielded
          cases yielded
          exact sentinel_below source holds _ _ _
        · simp only [code_bind_pure] at yielded
          cases yielded
          exact children_below source facts holds request scope complete before.native.machine valid ready _ arity

/-- Only reached native node and edge instructions require their actual machine-key checks. -/
def Words (width : Nat) : Control Output → Prop
  | .code (.node request _) => ∀ key,
      SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
        SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right
  | .code (.edge request _) => SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right
  | _ => True

/-- Word checks range over actual checked yielded prefixes and assume no completed result. -/
def WordRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : State width) : Prop :=
  ∀ fuel next after, Steps fuel control state next after → Words width next

/-- The zero-length actual checked prefix supplies its current request words. -/
theorem WordRanges.current [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : State width) (ranges : WordRanges control state) : Words width control :=
  ranges 0 control state (.refl _ _)

/-- A checked yielded prefix retains the word plan for its exact next control and full state. -/
theorem WordRanges.after_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control Output) (state after : State width) (ranges : WordRanges control state)
    (fuel : Nat) (trace : Steps fuel control state next after) : WordRanges next after := by
  intro extra final current rest
  exact ranges _ final current (trace.trans _ _ _ _ _ _ _ _ rest)

/-- One actual checked step retains the word plan through the resulting operation cache. -/
theorem WordRanges.after_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control Output) (state after : State width) (ranges : WordRanges control state)
    (one : step control state = .yielded next after) : WordRanges next after :=
  ranges.after_trace control next state after 1 (.cons _ _ _ _ _ _ 0 one (.refl _ _))

/-- Appending source code does not add a word obligation to an earlier instruction. -/
theorem words_before_bind (width : Nat) (control : Control A) (next : A → Code Symbol Guard B)
    (checked : Words width (control.bind next)) : Words width control := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact checked | trivial

/-- Every actual checked body prefix is a prefix of its appended continuation. -/
theorem WordRanges.before_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (next : A → Code Symbol Guard B) (state : State width)
    (ranges : WordRanges (control.bind next) state) : WordRanges control state := by
  intro fuel current after trace
  exact words_before_bind width current next (ranges fuel (current.bind next) after (trace.bind _ _ _ _ _ next))

/-- An actual trace to an inner return retains word checks at the exact appended continuation. -/
theorem WordRanges.after_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (next : A → Code Symbol Guard B) (state after : State width)
    (ranges : WordRanges (control.bind next) state) (fuel : Nat) (value : A)
    (trace : Steps fuel control state (.code (.pure value)) after) : WordRanges (.code (next value)) after := by
  have appended := trace.bind _ _ _ _ _ next
  exact ranges.after_trace (control.bind next) (.code (next value)) state after fuel appended

end MicroCFTA.SourceCurrentAllocatedNativeRequestBounds
