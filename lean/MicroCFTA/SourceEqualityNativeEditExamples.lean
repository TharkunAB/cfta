import MicroCFTA.SourceEqualityNativeClassEdits
import MicroCFTA.SourceEqualityNativeTargetExamples
import MicroCFTA.SourceClosedSelfHeadRepair

/-!
# Kernel checks for scoped native edit control and memo reuse

The examples retain root-list leaf priority, missing signed indexes, raw
closed cycles, and both exhausted traversal bounds. Two actual edit leaves
reuse one returned native node memo cell.
-/
namespace MicroCFTA.SourceEqualityNativeEditExamples
open InternedConstructorTemplates InternedNestedConstruction SourceEqualityNativeScoped SourceEqualityNativeEditWorker

/-- Node leaves invoke native intersection before empty checks; list-root leaves are ignored. -/
theorem leaf_priority (state : SourceRecursiveIntersectionThunks.State width Nat Unit) (target : Value Nat Unit) :
    edit () (fun _ _ => ()) 1 0 0 (.editAt target) .empty state =
      .native (.yielded (.node ⟨IntersectionEmptyDomain.emptyDomain, target, .empty⟩ .pure) state) ∧
    editAll () (fun _ _ => ()) 0 0 0 [([], target)] [.reference .depth] state = .done [.reference .depth] state := ⟨rfl, rfl⟩

/-- Missing signed child-list positions use no native callback or traversal bound. -/
theorem missing_positions (state : SourceRecursiveIntersectionThunks.State width Nat Unit) (target : Value Nat Unit) :
    editAll () (fun _ _ => ()) 0 0 0 [([-1], target), ([9], target)] [.reference .depth] state = .done [.reference .depth] state := rfl

/-- Observe actual raw self head completion with full native state retained. -/
def SelfResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending _ _ => False
  | .done value heap =>
      let state := SourceRecursiveIntersectionThunks.initial 8 ⟨heap, Cache.emptyState⟩
      edit () (fun _ _ => ()) 2 2 0 (.editBelow []) value state = .done .empty state ∧
      edit () (fun _ _ => ()) 1 2 0 (.editBelow []) value state = .exhausted .worker state ∧
      edit () (fun _ _ => ()) 2 1 0 (.editBelow []) value state = .exhausted .head state

/-- Raw recursive cycles normalize without changing either native memo table. -/
theorem raw_self : SelfResults
    (InternedFreshOrdinaryConstruction.build SourceClosedSelfRequireBoundary.expression [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

/-- Two different edit positions request the same actual native intersection. -/
def requests : List (SourceEqualityEdits.Path × Value Nat Unit) := [([0], .empty), ([1], .empty)]

/-- Observe the populated native state returned by both edit leaves. -/
def WarmResults : Result 8 Nat Unit (List (Value Nat Unit)) → Prop
  | .done values state => values = [.empty, .empty] ∧ state.nodes.next = 1 ∧ state.edges.next = 0 ∧
      editAll () (fun _ _ => ()) 1 0 16 requests [.empty, .empty] state = .done [.empty, .empty] state
  | _ => False

/-- Both leaves and a later repeated batch retain one identical returned native memo cell. -/
theorem warm_reuse : WarmResults
    (editAll () (fun _ _ => ()) 1 0 16 requests [.empty, .empty] SourceEqualityNativeTargetExamples.cold) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

end MicroCFTA.SourceEqualityNativeEditExamples
