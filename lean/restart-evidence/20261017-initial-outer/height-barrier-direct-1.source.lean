import MicroCFTA.SourceCurrentAllocatedGateWorker
import MicroCFTA.SourceEqualityRequiredWorkerSound
import MicroCFTA.SourceEqualityRequiredSemanticCache
import MicroCFTA.MergedOrdinaryHeight

/-!
# Ordinary-height growth at a source-accepted recursive path

A closed plain Mu passes the actual primary gate. Requiring one of its
children exposes an ordinary row node. Its ordinary height increases from
zero to one. This refutes nonincreasing ordinary height for Required on
the general source domain. It does not assert an outer cycle or a runtime bug.
-/
namespace MicroCFTA.SourceCurrentOuterHeightBarrier
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "height" => MergedOrdinaryHeight.height

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def annotation : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard := .binder false (.node [.mk ("step", .top) annotation [.var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def before := built.state
private def read := MergedFreshOrdinaryExposure.nodeEdges 0 original before
private def rows : List (EdgeValue Symbol Guard) := match read with | .done edges _ => edges | _ => []
private def middle := read.state
private def constructed := run (makeNode rows) middle
private def result := constructed.1
private def after := constructed.2
private def needed : SourceEqualityNeeded.Needed := .node [(0, .node [])]

private theorem built_done : built = .done original before := by cbv
private theorem available : Available before original :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result original before built_done
private theorem closed : original.free = [] := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady before :=
  SourceEqualityRequiredSemanticCache.constructed expression original before built_done
private theorem head : SourceEqualityRequiredHead.Head original before result after :=
  .read 0 rows middle (by cbv) rfl
private theorem required : SourceEqualityRequiredGraph.RequireNode needed original before result after :=
  SourceEqualityRequiredWorkerSound.require_graph 3 0 needed original before result after (by cbv)
private theorem primary : SourceCurrentMuEndpoint.classMeets true source reaches 1 [original, original]
    [[0, 0], [1, 0]] before = .done (some false) before := by cbv

/-- An actual closed plain source passes the gate and grows under its actual child requirement. -/
theorem supported_required_growth :
    ∃ (syntax : Syntax Symbol Guard) (input : Value Symbol Guard) (initial : Heap)
        (output : Value Symbol Guard) (final : Heap),
      InternedFreshOrdinaryConstruction.build syntax [] empty = .done input initial ∧
      SourceEqualityRequiredSemanticCache.SemanticReady initial ∧ Available initial input ∧ input.free = [] ∧
      source input = true ∧
      SourceCurrentMuEndpoint.classMeets true source reaches 1 [input, input] [[0, 0], [1, 0]] initial =
        .done (some false) initial ∧
      SourceEqualityRequiredHead.Head input initial output final ∧
      SourceEqualityRequiredGraph.RequireNode (.node [(0, .node [])]) input initial output final ∧
      SourceEqualityRequiredSemanticCache.SemanticReady final ∧ Available final output ∧ output.free = [] ∧
      height input = 0 ∧ height output = 1 := by
  have checked := head.verified semantic.ready available closed
  exact ⟨expression, original, before, result, after, built_done, semantic, available, closed,
    by cbv, primary, head, required,
    SourceEqualityRequiredSemanticCache.head head semantic available closed,
    checked.2.1, checked.2.2.1, by cbv, by cbv⟩

/-- Even closed, available, unconstrained inputs do not admit the old Required height bound. -/
theorem not_required_height_nonincreasing :
    ¬ (∀ (input output : Value Symbol Guard) (initial final : Heap),
      SourceEqualityRequiredSemanticCache.SemanticReady initial → Available initial input → input.free = [] →
      source input = true →
      SourceEqualityRequiredGraph.RequireNode (.node [(0, .node [])]) input initial output final →
      height output ≤ height input) := by
  intro bound
  obtain ⟨_syntax, input, initial, output, final, _built, ready, present, clean, plain,
    _primary, _head, required, _ready, _present, _clean, inputHeight, outputHeight⟩ := supported_required_growth
  have impossible := bound input output initial final ready present clean plain required
  rw [inputHeight, outputHeight] at impossible
  omega

end MicroCFTA.SourceCurrentOuterHeightBarrier
