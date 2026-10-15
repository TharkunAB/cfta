import MicroCFTA.SourceEqualityNativeTargetNarrowing
import MicroCFTA.SourceEqualityNativeProjection

/-!
# Kernel checks for source target-list order and warm memo reuse

Empty and singleton lists need no native request. Three operands retain the
source first seed and right fold. Repeated actual requests retain warm cells.
-/
namespace MicroCFTA.SourceEqualityNativeTargetExamples
open InternedConstructorTemplates SourceRecursiveIntersectionThunks SourceEqualityNativeTargetExecution

/-- Empty and singleton source lists complete without consuming a native request bound. -/
theorem source_shortcuts (state : State width Nat Unit) (value : Value Nat Unit) :
    intersectList () (fun _ _ => ()) 0 [] state = .done .empty state ∧
    intersectList () (fun _ _ => ()) 0 [value] state = .done value state := ⟨rfl, rfl⟩

/-- Three operands use the first as seed, then the third, then the second. -/
theorem source_order (state : State width Nat Unit) (first second third : Value Nat Unit) (fuel : Nat) :
    intersectList () (fun _ _ => ()) fuel [first, second, third] state =
      match SourceRecursiveIntersectionNative.execute () (fun _ _ => ()) fuel
          (.node ⟨IntersectionEmptyDomain.emptyDomain, third, first⟩ .pure) state with
      | .done tail middle => SourceRecursiveIntersectionNative.execute () (fun _ _ => ()) fuel
          (.node ⟨IntersectionEmptyDomain.emptyDomain, second, tail⟩ .pure) middle
      | other => other := by
  simp only [intersectList, fold]
  cases SourceRecursiveIntersectionNative.execute () (fun _ _ => ()) fuel
    (.node ⟨IntersectionEmptyDomain.emptyDomain, third, first⟩ .pure) state <;> rfl

/-- The actual initial native cache used by the empty-operand fixture. -/
def cold : State 8 Nat Unit := initial 8 ⟨InternedConstructorTemplates.empty, Cache.emptyState⟩

/-- The first request publishes one node cell; later folds reuse that exact returned state. -/
def WarmResults : SourceRecursiveIntersectionNative.Outcome 8 Nat Unit (Value Nat Unit) → Prop
  | .done value state => value = .empty ∧ state.nodes.next = 1 ∧ state.edges.next = 0 ∧
      intersectList () (fun _ _ => ()) 16 [.empty, .empty, .empty] cold = .done .empty state ∧
      intersectList () (fun _ _ => ()) 16 [.empty, .empty] state = .done .empty state
  | _ => False

/-- Two and three actual native requests preserve the same populated memo tables. -/
theorem warm_reuse : WarmResults (intersectList () (fun _ _ => ()) 16 [.empty, .empty] cold) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

end MicroCFTA.SourceEqualityNativeTargetExamples
