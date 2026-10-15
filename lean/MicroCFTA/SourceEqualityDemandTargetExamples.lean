import MicroCFTA.SourceEqualityClassTargetAPI

/-!
# Kernel checks for actual source target demands

Empty targets invoke no operand. Nonempty targets demand the original
forest paths. The source first seed is demanded after later operands.
Two actual intersections share one populated warm native cell.
-/
namespace MicroCFTA.SourceEqualityDemandTargetExamples
open InternedConstructorTemplates InternedNestedConstruction SourceEqualityNativeScoped SourceEqualityDemandTargetWorker

/-- An empty target invokes no projection, merge, or native request. -/
theorem empty_target (before : NativeState width Nat Unit) (values : List (Value Nat Unit)) :
    target () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 values [] before = .done .empty before := rfl

/-- Three source operands are demanded second, third, first before the two right-fold intersections. -/
theorem source_demand_order (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h c n : Nat) (values : List (Value Symbol Guard))
    (first second third : List Int) (before : NativeState width Symbol Guard) :
    target emptyGuard conjoin clear top p h c n values [first, second, third] before =
      (operand clear top p h c second values before).bind fun b middle =>
        (operand clear top p h c third values middle).bind fun d later =>
          (operand clear top p h c first values later).bind fun a seedState =>
            (leaf emptyGuard conjoin n d a seedState).bind fun tail tailState => leaf emptyGuard conjoin n b tail tailState := by
  simp only [target, fold]
  cases operand clear top p h c second values before with
  | projection | merge | native => rfl
  | done b middle =>
      simp only [Result.bind]
      cases operand clear top p h c third values middle with
      | projection | merge | native => rfl
      | done d later =>
          dsimp only
          cases operand clear top p h c first values later <;> rfl

/-- Observe demanded projections, actual ordinary merges, and both native requests on a constructed constant. -/
def WarmResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending .. => False
  | .done value heap =>
      let before := SourceRecursiveIntersectionThunks.initial 8 ⟨heap, Cache.emptyState⟩
      match target () (fun _ _ => ()) (fun _ => true) () 1 0 0 16 [value, value, value] [[0], [1], [2]] before with
      | .done result after => result = value ∧ after.machine.heap = heap ∧ after.nodes.next = 1 ∧ after.edges.next = 0 ∧
          target () (fun _ _ => ()) (fun _ => true) () 2 1 3 20 [value, value, value] [[0], [1], [2]] before = .done value after ∧
          target () (fun _ _ => ()) (fun _ => true) () 1 0 0 16 [value, value, value] [[0], [1], [2]] after = .done value after
      | _ => False

/-- Actual source operands and both target intersections retain one warm native cell at larger bounds and on repeated demand. -/
theorem warm_demand_reuse : WarmResults (InternedFreshOrdinaryConstruction.build (.node [.mk 11 () []]) [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

end MicroCFTA.SourceEqualityDemandTargetExamples
