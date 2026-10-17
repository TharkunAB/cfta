import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources

/-!
# Finite indexed queries that consume their actual earlier results

Each request selects two values from the current pool. The exact returned
value is appended before the next request. Initial index checks and one
numeric forecast construct all executions. Every actual return retains
its semantic receipts, populated caches, and the next resource bounds.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGeneratedQuerySequence
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Reserved advance)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits Receipt)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open InternedNestedProvenance (Values)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {width bits : Nat}

/-- Every request index selects an initial value or an actual preceding result. -/
def Supported : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | count, pair :: rest => pair.1 < count ∧ pair.2 < count ∧ Supported (count + 1) rest

/-- The current selection pool contains available closed values with one guard-depth bound. -/
structure Pool (depth : Nat) (values : List (Value Symbol Guard)) (state : Checked width) : Prop where
  /-- Each pool value remains available in the current physical heap. -/
  available : Values state.native.machine.heap values
  /-- Each pool value has no free recursion reference. -/
  closed : ∀ value ∈ values, value.free = []
  /-- Every pool value has the same admissible guard-depth bound. -/
  cap : ∀ value ∈ values, SourceCurrentConstrainedCap.Cap Plain depth value

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual query appends its literal result and retains every earlier pool value. -/
theorem Pool.after {profile : Profile} {depth : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {fuel : Nat} {left right value : Value Symbol Guard}
    {before after : Checked width} {memos : Memos} {values : List (Value Symbol Guard)}
    (pool : Pool depth values before)
    (receipt : Receipt profile depth formulas solver inventory fuel left right before value after memos) :
    Pool depth (values ++ [value]) after := by
  constructor
  · intro item member
    rcases List.mem_append.mp member with old | next
    · exact (pool.available item old).grows _ _ receipt.query.extension.heap receipt.query.extension.history
    · have same : item = value := by simpa only [List.mem_singleton] using next
      subst item
      exact receipt.query.available
  · intro item member
    rcases List.mem_append.mp member with old | next
    · exact pool.closed item old
    · have same : item = value := by simpa only [List.mem_singleton] using next
      subst item
      exact receipt.query.closed
  · intro item member
    rcases List.mem_append.mp member with old | next
    · exact pool.cap item old
    · have same : item = value := by simpa only [List.mem_singleton] using next
      subst item
      exact receipt.joint.cap

/-- A run retains each exact query receipt at the literal preceding return. -/
inductive Run (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (memos : Memos) :
    Profile → List (Nat × Nat) → List (Value Symbol Guard) → Checked (bits + 2) →
      List (Value Symbol Guard) → Checked (bits + 2) → Prop where
  /-- An empty query sequence retains the entire checked state. -/
  | nil : Run depth formulas solver memos profile [] pool before [] before
  /-- Both current operands and the next pool use the actual earlier values. -/
  | cons {inventory : Inventory} {fuel : Nat}
      (leftFound : pool[first]? = some left) (rightFound : pool[second]? = some right)
      (receipt : Receipt profile depth formulas solver inventory fuel left right before value middle memos)
      (tail : Run depth formulas solver memos (SourceCurrentAllocatedNativeResourceForecast.step profile)
        rest (pool ++ [value]) middle results after) :
      Run depth formulas solver memos profile ((first, second) :: rest) pool before (value :: results) after

/-- One actual result is returned for every requested pair. -/
theorem Run.length {depth : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {memos : Memos}
    {profile : Profile} {requests : List (Nat × Nat)} {pool results : List (Value Symbol Guard)}
    {before after : Checked (bits + 2)} (actual : Run depth formulas solver memos profile requests pool before results after) :
    results.length = requests.length := by
  induction actual with
  | nil => rfl
  | cons _ _ _ _ ih => exact congrArg Nat.succ ih

/-- One initial forecast constructs every supported finite sequence over original values and preceding results. -/
theorem complete_many (profile : Profile) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (requests : List (Nat × Nat)) (pool : List (Value Symbol Guard))
    (supported : Supported pool.length requests) (reserved : Reserved bits profile requests.length)
    (inventory : Inventory) (before : Checked (bits + 2)) (frame : Frame formulas solver inventory before)
    (fits : Fits profile before) (known : Pool depth pool before)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after next,
      Run depth formulas solver memos profile requests pool before results after ∧
      Frame formulas solver next after ∧ Fits (advance profile requests.length) after ∧
      Extension before.native.machine after.native.machine ∧ Pool depth (pool ++ results) after ∧
      Valid after.native.machine.heap memos ∧ results.length = requests.length := by
  induction requests generalizing profile pool inventory before with
  | nil => exact ⟨[], before, inventory, .nil, frame, fits, .refl _, by simpa only [List.append_nil] using known, valid, rfl⟩
  | cons pair rest ih =>
      obtain ⟨first, second, remaining⟩ := supported
      let left := pool[pair.1]'first
      let right := pool[pair.2]'second
      have leftMember : left ∈ pool := List.getElem_mem first
      have rightMember : right ∈ pool := List.getElem_mem second
      obtain ⟨next, fuel, value, middle, receipt⟩ := SourceCurrentConstrainedCapGeneratedQueryResources.complete profile depth
        formulas solver inventory before frame fits reserved.head left right (known.available left leftMember)
        (known.available right rightMember) (known.closed left leftMember) (known.closed right rightMember)
        (known.cap left leftMember) (known.cap right rightMember) memos valid
      have tailSupported : Supported (pool ++ [value]).length rest := by
        simpa only [List.length_append, List.length_singleton] using remaining
      obtain ⟨results, after, finalInventory, actual, finalFrame, finalFits, extension, finalPool, globals, count⟩ :=
        ih (SourceCurrentAllocatedNativeResourceForecast.step profile) (pool ++ [value]) tailSupported reserved.tail
          next middle receipt.frame receipt.fits (known.after receipt) receipt.query.globals
      refine ⟨value :: results, after, finalInventory,
        .cons (List.getElem?_eq_getElem first) (List.getElem?_eq_getElem second) receipt actual,
        finalFrame, finalFits, receipt.query.extension.trans extension, ?_, globals, congrArg Nat.succ count⟩
      simpa only [List.append_assoc, List.singleton_append] using finalPool

end MicroCFTA.SourceCurrentConstrainedCapGeneratedQuerySequence
