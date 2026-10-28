import MicroCFTA.SourcePruningEnumerationPrefixCoverage

/-!
# Uniform actual prefix coverage with the original completion packet

The original producer chooses its fuel before all semantic assignments.
Its complete admission and stable PrefixValid family remain unchanged.
The appended observer requires the original concrete narrowing policy.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
attribute [local instance] SourcePruningEnumerationAction.actionMonadList


/-- Original prefix completion retains its full packet and the accepted-assignment observer. -/
theorem prefix_complete_accepting
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos) (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ fuel, (∀ extra,
      PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (fuel + extra) uv caller before memos
        (runPrefix holeKey fits admits graph templates stop order metadata
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          uv caller before memos.query)) ∧
      ∀ extra (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          residualMeaning assignment before.core →
        (∀ symbol annotation child, assignment uv = .node symbol [child] →
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation child →
          admits (holeKey metadata.typing uv) annotation = true ∧ fits (holeKey metadata.typing uv) symbol = true) →
        (∀ annotation first second third fourth,
          assignment uv = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
          admits (holeKey metadata.typing uv) annotation = true) →
        (∀ annotation first second,
          assignment uv = .node ("filter", FullSyntax.Formula.top) [first, second] →
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
          admits (holeKey metadata.typing uv) annotation = true) →
        match runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query with
        | .parked _ (some after) _ =>
            Satisfies (SourcePruningEnumerationNativeLanguage.handles
              (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
              residualMeaning assignment after.core
        | .narrowed _ _ reached _ _ (some after) _ _ =>
            Satisfies (SourcePruningEnumerationNativeLanguage.handles
              (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap)
              residualMeaning assignment after.core
        | _ => False := by
  obtain ⟨fuel, running⟩ := prefix_complete holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before preference uv roots initial safe pending selection realized paths counts flags
  refine ⟨fuel, running, ?_⟩
  intro extra ambient residualMeaning assignment satisfied unary application filtered
  have ready := SourcePruningEnumerationSelection.ready caller.checked.native.machine.heap before preference uv
    safe roots paths counts flags selection
  exact prefix_accepting holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory (fuel + extra) uv caller before memos initial ready realized (running extra)
    ambient residualMeaning assignment satisfied unary application filtered

end MicroCFTA.SourcePruningEnumerationSelectedStep
