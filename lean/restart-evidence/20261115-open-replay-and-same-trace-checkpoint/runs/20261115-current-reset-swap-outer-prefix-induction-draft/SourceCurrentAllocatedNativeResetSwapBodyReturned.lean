import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult

/-!
# Reset and swap bodies retain the real outer query prefix

The selected raw body is already its literal child query.
Its remaining budget decreases only from the original outer query budget.
The same emitted continuation qualifies each actual smaller child run.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeResetSwapBodyReturned
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

/-- Reset and swap transfer both laws and actual child results at the unchanged remaining budget. -/
theorem reset_swap_body_of_outer_query_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (valueLaw : Value Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (parent first : Checked width) (parentFuel : Nat)
    (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap)
    (origin : Steps 1 (.code (.node request .pure)) parent
      (.code ((compileNode request).bind next)) first)
    (nodes : Returned nodeLaw first.native.nodes) (edges : Returned edgeLaw first.native.edges)
    (children : ∀ child : NodeRequest Symbol Guard,
      ((SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset ∧
          child = ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩) ∨
        (SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap ∧
          child = ⟨request.domain, request.right, request.left⟩)) →
      ∀ childFuel, childFuel < parentFuel →
      Steps 1 (.code (.node request .pure)) parent
        (.code ((requestNode child.domain child.left child.right).bind next)) first →
      Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestNode child.domain child.left child.right)) first).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestNode child.domain child.left child.right)) first).state.native.edges ∧
      (∀ (value : Value Symbol Guard) (after : Checked width),
        Steps childFuel (.code (requestNode child.domain child.left child.right)) first
          (.code (.pure value)) after → valueLaw value)) :
    ∃ child : NodeRequest Symbol Guard,
      ((SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset ∧
          child = ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩) ∨
        (SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap ∧
          child = ⟨request.domain, request.right, request.left⟩)) ∧
      compileNode request = requestNode child.domain child.left child.right ∧
      Steps 1 (.code (.node request .pure)) parent
        (.code ((requestNode child.domain child.left child.right).bind next)) first ∧
      (∀ remaining, remaining < parentFuel →
        Returned nodeLaw (SourceEqualityNativeDemand.execute remaining
          (.code (compileNode request)) first).state.native.nodes ∧
        Returned edgeLaw (SourceEqualityNativeDemand.execute remaining
          (.code (compileNode request)) first).state.native.edges ∧
        (∀ count, count ≤ remaining → ∀ (value : Value Symbol Guard) (after : Checked width),
          Steps count (.code (compileNode request)) first (.code (.pure value)) after → valueLaw value) ∧
        (∀ (value : Value Symbol Guard) (after : Checked width),
          SourceEqualityNativeDemand.execute remaining (.code (compileNode request)) first =
            .done value after → valueLaw value)) := by
  obtain ⟨child, branch, compiled⟩ :
      ∃ child : NodeRequest Symbol Guard,
        ((SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .reset ∧
            child = ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩) ∨
          (SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .swap ∧
            child = ⟨request.domain, request.right, request.left⟩)) ∧
        compileNode request = requestNode child.domain child.left child.right := by
    rcases selected with reset | swap
    · refine ⟨⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩, .inl ⟨reset, rfl⟩, ?_⟩
      simp only [compileNode, reset]
    · refine ⟨⟨request.domain, request.right, request.left⟩, .inr ⟨swap, rfl⟩, ?_⟩
      simp only [compileNode, swap]
  have childOrigin : Steps 1 (.code (.node request .pure)) parent
      (.code ((requestNode child.domain child.left child.right).bind next)) first := by
    simpa only [compiled] using origin
  refine ⟨child, branch, compiled, childOrigin, ?_⟩
  intro remaining shorter
  have childLaws := children child branch remaining shorter childOrigin nodes edges
  have pureResults : ∀ count, count ≤ remaining → ∀ (value : Value Symbol Guard) (after : Checked width),
      Steps count (.code (compileNode request)) first (.code (.pure value)) after → valueLaw value := by
    intro count bounded value after actual
    have smaller := children child branch count (by omega) childOrigin nodes edges
    apply smaller.2.2 value after
    simpa only [compiled] using actual
  refine ⟨?_, ?_, pureResults, ?_⟩
  · simpa only [compiled] using childLaws.1
  · simpa only [compiled] using childLaws.2.1
  · intro value after done
    obtain ⟨count, bounded, actual⟩ := done_trace remaining _ first after value done
    exact pureResults count (Nat.le_of_lt bounded) value after actual

end MicroCFTA.SourceCurrentAllocatedNativeResetSwapBodyReturned
