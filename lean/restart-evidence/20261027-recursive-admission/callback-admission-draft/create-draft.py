from pathlib import Path
base=Path('/tmp/mcfta-recursive-admission-20261027/callback-admission-draft')
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
old=(repo/'SourcePruningEnumerationHeadAdmission.lean').read_text()
start=old.index('theorem head_finite_complete_resources_with_receipt\n')
end=old.index(' := by',start)
contract=old[start:end].replace('theorem head_finite_complete_resources_with_receipt\n','theorem head_finite_complete_resources_with_callback_admission\n',1)
last='      ∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),'
assert contract.count(last)==1
contract=contract.replace(last,'      (∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),',1)+') ∧\n'+'''      ∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),
        receipt = .complete fragment reached queries after →
        SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver middleInventory reached middleMemos
          metadata after uv fragment recursiveFuel (afterHead seed inherited) (massCeil seed capturedMass inherited)'''
preamble='''import MicroCFTA.SourcePruningEnumerationHeadAdmission
import MicroCFTA.SourcePruningEnumerationFiniteCallbackReceiptLanguage

/-!
# Original resource admission at an actual completed callback input

A completed head retains the planned callback seed and mass ceiling.
The original reservation supplies the smaller-depth callback reservation.
An actual false callback retains this admission at its returned frame.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing : Type} {bits : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- The actual callback input retains its original finite resource admission. -/
structure RecursiveCallbackAdmission
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (uv : Nat) (fragment : Fragments.Fragment Symbol) (recursiveFuel : Nat) (seed : Seed) (ceiling : Nat) : Prop where
  /-- The callback uses this actual native caller, full memo state and cache. -/
  packet : Packet formulas solver inventory caller memos metadata before
  /-- Every fragment hole names an allocated input variable. -/
  allocated : FragmentBound before.core.counter fragment
  /-- The actual native caller fits the planned callback profile. -/
  bounded : Fits seed.2 caller.checked
  /-- Every current native guard belongs to the planned callback carrier. -/
  known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap
  /-- The actual input cache fits the original mass ceiling. -/
  mass : suspendedBound before.core ≤ ceiling
  /-- The original reservation pays the smaller-depth recursive callback. -/
  reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling

variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq Node]

/-- An actual false callback retains the same seed, mass ceiling and reservation. -/
theorem RecursiveCallbackAdmission.after_false
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {metadata : Metadata Typing} {uv : Nat} {fragment : Fragments.Fragment Symbol}
    {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
    {checkEmpty : Bool} {edgesOf : Node → List (InternedConstructorTemplates.EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {recursiveFuel fuel : Nat} {updated : Metadata Typing} {after : Core}
    {outcome : SourcePruningEnumerationNativeContinuations.HookResult
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)}
    {seed : Seed} {ceiling : Nat}
    (admission : RecursiveCallbackAdmission formulas solver inventory caller memos metadata before uv fragment
      recursiveFuel seed ceiling)
    (receipt : FalseCallbackReceipt holeKey fits admits formulas solver inventory graph templates metadata uv fragment
      caller memos before checkEmpty edgesOf stop order recursiveFuel fuel updated after outcome) :
    RecursiveCallbackAdmission formulas solver inventory caller memos updated
      (EnumerationExpandableIndex.frame after before) uv fragment recursiveFuel seed ceiling := by
  refine ⟨receipt.returned, ?_, admission.bounded, admission.known, ?_, admission.reserved⟩
  · change FragmentBound after.counter fragment
    rw [receipt.frame.counter]
    exact admission.allocated
  · change suspendedBound after ≤ ceiling
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after receipt.frame.values]
    exact admission.mass

end MicroCFTA.SourcePruningEnumerationRecursive

'''
# Copy the original head namespace declarations and local aliases unchanged.
head=old[old.index('namespace MicroCFTA.SourcePruningEnumerationNativeHookResources'):old.index('/-- The current input and its original edge reservation')]
# Original class split is not needed because the new theorem uses all runtime declarations.
head+='variable [DecidableEq Symbol] [DecidableEq Node]\n\n'
body=''' := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    running, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown, shape, completedReceipt⟩ :=
    head_finite_complete_resources_with_receipt holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges
      depth free edge packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    running, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown, shape, completedReceipt, ?_⟩
  intro fragment reached queries after completed
  have actualReceipt := completedReceipt fragment reached queries after completed
  have actualAdmitted : Admitted uv (.complete fragment reached queries after) := by
    simpa only [completed] using admitted
  have actualMass := SourcePruningEnumerationRecursiveReservation.head_mass_le seed capturedMass inherited
    before scs receipt initialMass inheritedLength cacheBounds
  have mass : suspendedBound after.core ≤ massCeil seed capturedMass inherited := by
    simpa only [completed] using actualMass
  exact ⟨actualReceipt.completed, actualAdmitted.2.2.1,
    actualReceipt.bounded, actualReceipt.known, mass, reserved.2⟩

end MicroCFTA.SourcePruningEnumerationNativeHookResources
'''
source=preamble+head+'/-- Keep the full actual head packet and append the original callback resource admission. -/\n'+contract+body
path=base/'SourcePruningEnumerationCallbackAdmission.lean'
assert not path.exists()
path.write_text(source)
(base/'revisions/v1/SourcePruningEnumerationCallbackAdmission.lean').write_text(source)
print(path)
print(len(source.splitlines()),len(source.encode()))
