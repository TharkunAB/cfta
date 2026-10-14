import MicroCFTA.SourceRecursiveIntersectionProductEdgeReadback
import MicroCFTA.SourceRecursiveIntersectionScheduleConstructors
import MicroCFTA.IntersectWalkRelated

/-!
# Actual guarded rows transport semantic schedule correspondence

Equal-arity rows retain all ordered child requests and the complete guard
conjunction. An arity mismatch has no term because of its actual empty
child. Node normalization retains the language of all returned rows.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionScheduleConstructors (Corresponds EdgeCorresponds)

/-- Equal-arity replay transports semantic child calls through the actual complete guarded edge. -/
theorem edge_schedule_body [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (sameArity : left.children.length = right.children.length) (row : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right state = .done row state)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (action : Value Symbol Guard × Value Symbol Guard → Except IntersectSchedule.Error (Shape (BinderLanguage.Payload Symbol)))
    (children : ∀ pair ∈ left.children.zip right.children, ∀ child,
      call domain pair.1 pair.2 state = .done child state → ∃ shape, action pair = .ok shape ∧ Corresponds holds child shape) :
    ∃ shapes, IntersectSchedule.walk action (left.children.zip right.children) = .ok shapes ∧
      EdgeCorresponds holds row (.branch ⟨left.entry.key.symbol, fun term =>
        holds left.entry.key.constraint term = true ∧ holds right.entry.key.constraint term = true⟩ shapes) := by
  obtain ⟨symbol, guard, paired⟩ := edge_children_replay emptyGuard conjoin call calls replay domain
    left right state valid known leftResident rightResident sameArity row done
  have related := SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ paired
    (fun pair member child _ completed => children pair member child completed)
  obtain ⟨shapes, walked, meanings⟩ := IntersectSchedule.walk_related action (Corresponds holds) _ _ related
  refine ⟨shapes, walked, ?_⟩
  cases row with
  | mk entry values =>
      change entry.key.symbol = left.entry.key.symbol at symbol
      change entry.key.constraint = conjoin left.entry.key.constraint right.entry.key.constraint at guard
      have actual := SourceRecursiveIntersectionScheduleConstructors.edge holds entry values shapes meanings
      simpa only [symbol, guard, conjoined, Bool.and_eq_true] using actual

/-- An actual arity-mismatch row has precisely the empty semantic shape, for every guard interpretation. -/
theorem edge_schedule_mismatch [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state)
    (different : left.children.length ≠ right.children.length) (row : EdgeValue Symbol Guard) (after : Machine Symbol Guard)
    (done : edge emptyGuard conjoin call left right state = .done row after)
    (holds : Guard → Term Symbol → Bool) : EdgeCorresponds holds row .empty := by
  have fields := edge_mismatch_readback emptyGuard conjoin call left right state valid different row after done
  cases row with
  | mk entry children =>
      have emptyChild : children = [.empty] := fields.2.2.1
      intro ambient
      funext term
      apply propext
      rw [InternedGuardedLanguage.edgeMeaning, BinderLanguage.meaning]
      constructor
      · rintro ⟨terms, _, accepted, _⟩
        rw [emptyChild] at accepted
        cases terms <;> simp only [InternedGuardedLanguage.forest, InternedGuardedLanguage.meaning, false_and] at accepted
      · exact False.elim

/-- Actual ordered edge work and node normalization transport local edge correspondences. -/
theorem node_schedule_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ row ∈ left, EdgeResident state.heap row) (rightResident : ∀ row ∈ right, EdgeResident state.heap row)
    (value : Value Symbol Guard) (done : node emptyGuard conjoin (call domain) left right state = .done value state)
    (holds : Guard → Term Symbol → Bool)
    (action : EdgeValue Symbol Guard × EdgeValue Symbol Guard → Except IntersectSchedule.Error (Shape (BinderLanguage.Payload Symbol)))
    (children : ∀ pair ∈ pairs left right, ∀ row,
      edge emptyGuard conjoin (call domain) pair.1 pair.2 state = .done row state →
      ∃ shape, action pair = .ok shape ∧ EdgeCorresponds holds row shape) :
    ∃ shapes, IntersectSchedule.walk action (pairs left right) = .ok shapes ∧ Corresponds holds value (.alternatives shapes) := by
  obtain ⟨rows, after, trace, built, _⟩ := node_readback emptyGuard conjoin call calls domain
    left right state valid known leftResident rightResident value state done
  have walked := (walk_done_iff _ _ _ _ _).mpr trace
  have checked := rows_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  have afterValid : Valid after := by simpa only [walked, Result.state] using checked.valid
  have resident := checked.result rows after walked
  have growth : Extension after state := by simpa only [built, Result.state] using work_extension (makeNode rows) after afterValid
  have paired := rows_pointwise_replay emptyGuard conjoin call calls replay domain left right state state rows after
    valid known leftResident rightResident walked growth
  have related := SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ paired
    (fun pair member row _ completed => children pair member row completed)
  obtain ⟨shapes, completed, meanings⟩ := IntersectSchedule.walk_related action (EdgeCorresponds holds) _ _ related
  have rebuilt := work_replay (makeNode rows) after state value state afterValid built (.refl _)
  refine ⟨shapes, completed, ?_⟩
  rw [(work_done (makeNode rows) state value state rebuilt).1]
  exact SourceRecursiveIntersectionScheduleConstructors.makeNode holds rows shapes meanings state.heap valid.1
    (fun row member => edge_grows _ _ growth.heap row (resident row member))

end MicroCFTA.SourceRecursiveIntersectionKernel
