import MicroCFTA.SourcePruningEnumerationSelectedStep

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}

/-- The initial root read and recursion check agree at every positive fuel. -/
private theorem runPrefix_initial_read_check_fuel
    (narrow : Metadata Typing → Nat → Nat → Node → Heap →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readExtra checkExtra nativeFuel representativeFuel indexFuel callbackFuel handle : Nat)
    (caller : Caller width) (queries : SourceEndpointMemo.Memos)
    (expandable : Nat → Bool) (waiting : EnumerationWaitingIndex.Waiting) :
    let before : EnumerationExpandableIndex.Cached Symbol Constraint :=
      ⟨EnumerationState.initial handle, expandable, waiting⟩
    runPrefixWithNarrow narrow graph templates stop order metadata
        (readExtra + 1) (checkExtra + 1) nativeFuel representativeFuel indexFuel callbackFuel
        0 caller before queries =
      runPrefixWithNarrow narrow graph templates stop order metadata
        1 1 nativeFuel representativeFuel indexFuel callbackFuel 0 caller before queries := by
  rfl

end MicroCFTA.SourcePruningEnumerationSelectedStep

#print axioms MicroCFTA.SourcePruningEnumerationSelectedStep.runPrefix_initial_read_check_fuel
